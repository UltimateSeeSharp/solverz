"""Contraction, then lift (I16): mirrors `LiftSearch.lean` node for node and writes row files.

liftrows.py stats <id> <ms> <ds> <k> <lam>          counts, no file
liftrows.py write <part> <id>:<ms>:<ds>:<k>:<lam> ...  writes lean/SignedDifferenceSets/LiftRows/PartNN.lean

ms, ds: comma lists, ds factorwise dividing ms (pad with 1). Phase 1 (`cover`) lists the coset-sum
vectors on Grp ds with sum s and |Y0| largest; phase 2 (`liftGo`) lifts each with its own coset
order (fewest patterns first) and the coset-fixing affine maps x -> x + k0 + psi(q x).
Nothing is imported or run on import.
"""
import itertools
import math
import os
import sys

CAP1 = 12000     # phase-1 nodes per declaration (calibrated 2026-11-07: 6000 nodes ~ 1 GB)
CAP2 = 3000      # phase-2 pattern evaluations per declaration (calibrated: 1500 ~ 1 GB)
MAXMAPS = 64


def num(ms, xs):
    y = 0
    for m, x in zip(ms, xs):
        y = y * m + x
    return y


def coords(ms, y):
    out = []
    for m in reversed(ms):
        out.append(y % m)
        y //= m
    return out[::-1]


class Row:
    def __init__(self, rid, ms, ds, k, lam):
        self.rid, self.ms, self.ds, self.k, self.lam = rid, ms, ds, k, lam
        self.v = math.prod(ms)
        self.n = math.prod(ds)
        self.c = self.v // self.n
        assert self.c * self.n == self.v and all(m % d == 0 for m, d in zip(ms, ds))
        S = k + lam * (self.v - 1)
        self.s = math.isqrt(S)
        assert self.s * self.s == S
        v, n = self.v, self.n
        self.add = [[num(ms, [(a + b) % m for a, b, m in zip(coords(ms, x), coords(ms, y), ms)])
                     for y in range(v)] for x in range(v)]
        self.hadd = [[num(ds, [(a + b) % d for a, b, d in zip(coords(ds, x), coords(ds, y), ds)])
                      for y in range(n)] for x in range(n)]
        self.q = [self.qidx(ms, ds, x) for x in range(v)]
        assert self.q == [num(ds, [a % d for a, d in zip(coords(ms, x), ds)]) for x in range(v)]
        self.neg = [next(y for y in range(v) if self.add[y][g] == 0) for g in range(v)]

    @staticmethod
    def qidx(ms, ds, y):
        """`qIdx` as Lean defines it."""
        if len(ms) == 1:
            return y % ds[0]
        if len(ms) == 0:
            return 0
        P = math.prod(ms[1:])
        return Row.qidx(ms[1:], ds[1:], y % P) + math.prod(ds[1:]) * (y // P % ds[0])

    # ---- phase 1 (`cover`, `coverGo`, `coverNodes`) ----
    def p1_params(self):
        c, k, lam = self.c, self.k, self.lam
        return c, k + lam * (c - 1), lam * c, k, self.s

    def cut(self, rem, sm, sq):
        c, Q, _, _, s = self.p1_params()
        return Q - sq < 0 or rem * (Q - sq) < (s - sm) ** 2 or rem * c < abs(s - sm)

    def leaf_ok(self, w, sm, sq, ab):
        c, Q, t, k, s = self.p1_params()
        n = self.n
        return (sm == s and sq == Q and ab <= k and (k - ab) % 2 == 0 and
                all(g == 0 or sum(w[x] * w[self.hadd[x][g]] for x in range(n)) == t
                    for g in range(n)))

    def cover_go(self, top, rem, pre, sm, sq, ab, out, cnt):
        """Visits coverGo's nodes; collects passing leaves; returns the node count."""
        cnt[0] += 1
        if rem == 0:
            w = pre[::-1]
            if self.leaf_ok(w, sm, sq, ab):
                out.append(tuple(w))
            return
        if self.cut(rem, sm, sq):
            return
        Q = self.p1_params()[1]
        for x in range(-top, top + 1):
            if Q - sq < x * x:
                continue
            self.cover_go(top, rem - 1, [x] + pre, sm + x, sq + x * x, ab + abs(x), out, cnt)

    def cover_front(self, d, top, rem, pre, sm, sq, ab, out):
        if d == 0 or rem == 0:
            out.append((top, rem, pre, sm, sq, ab))
            return
        if self.cut(rem, sm, sq):
            return
        Q = self.p1_params()[1]
        for x in range(-top, top + 1):
            if Q - sq < x * x:
                continue
            self.cover_front(d - 1, top, rem - 1, [x] + pre, sm + x, sq + x * x, ab + abs(x), out)

    def cover_nodes(self, d):
        c, Q, _, _, s = self.p1_params()
        out = []
        if self.cut(self.n, 0, 0):
            return out
        for x in range(-c, c + 1):
            if Q < x * x:
                continue
            self.cover_front(d, abs(x), self.n - 1, [x], x, x * x, abs(x), out)
        return out

    def phase1(self, d):
        nodes = self.cover_nodes(d)
        vecs, costs = [], []
        for nd in nodes:
            cnt = [0]
            self.cover_go(*nd, vecs, cnt)
            costs.append(cnt[0])
        return nodes, costs, vecs

    # ---- maps (`mapOK`) ----
    def maps(self):
        v, n, ds, add, q = self.v, self.n, self.ds, self.add, self.q
        K = [x for x in range(v) if q[x] == 0]
        gens = [(i, d) for i, d in enumerate(ds) if d > 1]
        def mul(t, x):
            y = 0
            for _ in range(t):
                y = add[y][x]
            return y
        homs = []
        for imgs in itertools.product(K, repeat=len(gens)):
            if any(mul(d, im) != 0 for (i, d), im in zip(gens, imgs)):
                continue
            psi = []
            for a in range(n):
                cs = coords(ds, a)
                y = 0
                for (i, d), im in zip(gens, imgs):
                    y = add[y][mul(cs[i], im)]
                psi.append(y)
            homs.append(psi)
        out = []
        for k0 in K:
            for psi in homs:
                al = [add[x][add[k0][psi[q[x]]]] for x in range(v)]
                if al != list(range(v)) and al not in out:
                    out.append(al)
        for al in out:
            assert self.map_ok(al)
        return out[:MAXMAPS]

    def map_ok(self, al):
        v, add, q, neg = self.v, self.add, self.q, self.neg
        if sorted(al) != list(range(v)):
            return False
        sig = lambda g: add[al[g]][neg[al[0]]]
        return all(q[al[x]] == q[x] and all(al[add[x][g]] == add[al[x]][sig(g)] for g in range(v))
                   for x in range(v))

    # ---- phase 2 (`liftGo`, `mkStep`, `liftFront`) ----
    @staticmethod
    def pats_of(l, y):
        if l == 0:
            return [[]] if y == 0 else []
        return ([[1] + p for p in Row.pats_of(l - 1, y - 1)] + [[0] + p for p in Row.pats_of(l - 1, y)] +
                [[2] + p for p in Row.pats_of(l - 1, y + 1)])

    def order(self, Y):
        c = self.c
        return sorted(range(self.n), key=lambda j: len(self.pats_of(c, Y[j])))

    def steps(self, Y, ord_, maps, m):
        v, q, add = self.v, self.q, self.add
        cos = [[x for x in range(v) if q[x] == a] for a in range(self.n)]
        out = []
        for t, j in enumerate(ord_):
            S = set(ord_[:t + 1])
            zs = [z for a in ord_[:t + 1] for z in cos[a]]
            out.append(dict(
                xs=cos[j], pats=self.pats_of(len(cos[j]), Y[j]),
                R=[sum(1 for x in range(v) if not (q[x] in S and q[add[x][g]] in S)) for g in range(v)],
                zs=zs, imgs=[[al[z] for z in zs] for al in maps] if t < m else []))
        return out

    def lift_go(self, sts, i, F, acc, cnt, front=None, d=None):
        """liftGo from step i; F: values (None unassigned); returns True when all cut."""
        if front is not None and (d == 0 or i == len(sts)):
            front.append((i, list(F), list(acc)))
            return True
        if i == len(sts):
            return False
        st = sts[i]
        v, add, neg, k, lam = self.v, self.add, self.neg, self.k, self.lam
        val = lambda y: F[y] or 0
        ok_all = True
        for p in st["pats"]:
            cnt[0] += 1
            vals = [1 if u == 1 else -1 if u == 2 else 0 for u in p]
            old = list(F)
            for x, w in zip(st["xs"], vals):
                F[x] = w
            new = list(acc)
            for g in range(v):
                dlt = 0
                for x, w in zip(st["xs"], vals):
                    if w:
                        dlt += w * ((F[add[x][g]] or 0) + (old[add[x][neg[g]]] or 0))
                new[g] += dlt
            cut = abs(k - new[0]) > st["R"][0] or any(abs(lam - new[g]) > st["R"][g] for g in range(1, v))
            if not cut:
                code = lambda y: 2 if F[y] == 1 else 1 if F[y] == -1 else 0
                cz = [code(z) for z in st["zs"]]
                cut = any([code(y) for y in im] < cz for im in st["imgs"])
            if not cut:
                if front is not None:
                    self.lift_go(sts, i + 1, F, new, cnt, front, d - 1)
                elif not self.lift_go(sts, i + 1, F, new, cnt):
                    ok_all = False
            F[:] = old
            if not ok_all:
                return False
        return ok_all

    def phase2(self, Y, maps, m, d):
        ord_ = self.order(Y)
        sts = self.steps(Y, ord_, maps, m)
        front = []
        self.lift_go(sts, 0, [None] * self.v, [0] * self.v, [0], front, d)
        costs, ok = [], True
        for (i, F, acc) in front:
            cnt = [0]
            r = self.lift_go(sts, i, list(F), list(acc), cnt)
            ok = ok and r
            costs.append(cnt[0])
        return ord_, front, costs, ok


def slices(costs, cap):
    cuts, cur = [], 0
    for i, cst in enumerate(costs):
        if cur and cur + cst > cap:
            cuts.append(i)
            cur = 0
        cur += cst
    cuts.append(len(costs))
    return cuts


def pick_depth(fn, cap, dmax):
    """Least depth whose largest node fits under cap."""
    for d in range(dmax + 1):
        r = fn(d)
        if max(r[1], default=0) <= cap or d == dmax:
            return d, r


def lst(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def wrap(line, indent=4, width=100):
    """Breaks a Lean line at spaces (after commas first) so no line passes `width`."""
    out, cur = [], line
    while len(cur) > width:
        cut = cur.rfind(", ", 0, width - 1)
        cut = cut + 1 if cut > indent + 8 else cur.rfind(" ", 0, width)
        out.append(cur[:cut].rstrip())
        cur = " " * indent + cur[cut:].lstrip()
    out.append(cur)
    return out


def gen_row(row, out):
    rid = row.rid.lower()
    ms, ds, k, lam, c, s = row.ms, row.ds, row.k, row.lam, row.c, row.s
    d1, (nodes1, costs1, vecs) = pick_depth(row.phase1, CAP1, row.n - 1)
    maps = row.maps()
    m = row.n
    ents, stats = [], []
    for Y in vecs:
        best = None
        for d in range(row.n + 1):
            r = row.phase2(Y, maps, m, d)
            best = (d, r)
            if max(r[2], default=0) <= CAP2:
                break
        d2, (ord_, front, costs2, ok) = best
        assert ok, f"{row.rid}: lift found for {Y}"
        ents.append((Y, ord_, d2, front, costs2))
        stats.append(sum(costs2))
    G = " × ".join(f"ZMod {x}" for x in ms)
    lines = []
    w = lambda ln: lines.extend(wrap(ln))
    w(f"/-- {row.rid}'s coset-fixing affine maps of `Grp {lst(ms)}` over `Grp {lst(ds)}`. -/")
    w(f"def {rid}Maps : List (List ℕ) := [")
    for i, al in enumerate(maps):
        w(f"  {lst(al)}" + ("," if i + 1 < len(maps) else "]"))
    if not maps:
        w("  ]")
    w("")
    for i, (Y, ord_, d2, _, _) in enumerate(ents):
        w(f"/-- {row.rid}, coset-sum vector {i} (phase 1). -/")
        w(f"def {rid}Y{i} : List ℤ := {lst(Y)}")
        w("")
        w(f"/-- {row.rid}, the coset order for vector {i}. -/")
        w(f"def {rid}O{i} : List ℕ := {lst(ord_)}")
        w("")
    w(f"/-- {row.rid}'s vectors with their coset orders and map-cut depths. -/")
    w(f"def {rid}E : List (List ℤ × List ℕ × ℕ) := [" +
      ", ".join(f"({rid}Y{i}, {rid}O{i}, {m})" for i in range(len(ents))) + "]")
    w("")
    w(f"theorem {rid}_maps : mapsRow {lst(ms)} {lst(ds)} {rid}Maps = true := by")
    w("  decide +kernel")
    w("")
    cuts1 = slices(costs1, CAP1)
    for i in range(len(cuts1)):
        a = 0 if i == 0 else cuts1[i - 1]
        w(f"theorem {rid}_cover{i} : coverSlice {lst(ds)} {c} {k} ({lam}) {s} ({rid}E.map Prod.fst) {d1} {a} "
          f"{cuts1[i]} = true := by")
        w("  decide +kernel")
        w("")
    w(f"/-- {row.rid}, phase 1: {len(vecs)} vectors, {sum(costs1)} nodes in {len(cuts1)} slices. -/")
    w(f"theorem {rid}_cover : coverRow {lst(ds)} {c} {k} ({lam}) {s} ({rid}E.map Prod.fst) = true :=")
    w(f"  coverRow_of_slices (d := {d1}) {lst(cuts1)} (by decide +kernel) <|")
    for i in range(len(cuts1)):
        w(f"    .cons {rid}_cover{i} <|")
    w("    .single")
    w("")
    for yi, (Y, ord_, d2, front, costs2) in enumerate(ents):
        cuts2 = slices(costs2, CAP2)
        args = f"{lst(ms)} {lst(ds)} {rid}Y{yi} {rid}O{yi} {rid}Maps {m} {k} ({lam})"
        for i in range(len(cuts2)):
            a = 0 if i == 0 else cuts2[i - 1]
            w(f"theorem {rid}_y{yi}_s{i} : liftSlice {args} {d2} {a} {cuts2[i]} = true := by")
            w("  decide +kernel")
            w("")
        w(f"/-- {row.rid}, vector {yi}: {sum(costs2)} patterns tried, {len(cuts2)} slices. -/")
        w(f"theorem {rid}_y{yi} : liftRow {args} = true :=")
        w(f"  liftRow_of_slices (d := {d2}) {lst(cuts2)} (by decide +kernel) <|")
        for i in range(len(cuts2)):
            w(f"    .cons {rid}_y{yi}_s{i} <|")
        w("    .single")
        w("")
    w(f"/-- {row.rid}: no SDS ({row.v}, {k}, {lam}) in {G}: contraction to `Grp {lst(ds)}` (c = {c}),")
    w(f"{len(vecs)} vectors, {sum(stats)} patterns tried in the lifts. -/")
    w(f"theorem {rid}_not_hasSDS : ¬ HasSDS ({G}) {k} {lam} :=")
    w(f"  not_hasSDS_of_lift (ms := {lst(ms)}) (ds := {lst(ds)}) (c := {c}) (s := {s}) {rid}E")
    w(f"    (by decide +kernel) {rid}_cover {rid}_maps")
    w("    ⟨" + ", ".join(f"{rid}_y{i}" for i in range(len(ents))) + (", trivial⟩ _" if ents else "trivial⟩ _"))
    w("")
    out.extend(lines)
    return dict(p1=sum(costs1), p1slices=len(cuts1), vecs=len(vecs), maps=len(maps),
                p2=sum(stats), p2slices=sum(len(slices(e[4], CAP2)) for e in ents))


HEADER = """module

public import SignedDifferenceSets.LiftSearch

/-!
# Rows killed by contraction, then lift (I16), part {part}

{desc} Each by `not_hasSDS_of_lift`: phase 1 lists the coset-sum vectors on the quotient,
phase 2 rules out a lift of each (generated by `solver/liftrows.py`).
-/

@[expose] public section

namespace SignedDifferenceSets.LiftRows

open LiftSearch

set_option maxRecDepth 100000
set_option Elab.async false
"""


def parse(spec):
    rid, ms, ds, k, lam = spec.split(":")
    return Row(rid, [int(x) for x in ms.split(",")], [int(x) for x in ds.split(",")], int(k), int(lam))


def main():
    if sys.argv[1] == "stats":
        row = Row(sys.argv[2], *[[int(x) for x in a.split(",")] for a in sys.argv[3:5]],
                  int(sys.argv[5]), int(sys.argv[6]))
        out = []
        print(gen_row(row, out))
        return
    part = int(sys.argv[2])
    rows = [parse(a) for a in sys.argv[3:]]
    body, info = [], []
    for row in rows:
        st = gen_row(row, body)
        info.append(f"{row.rid} {st}")
        print(row.rid, st, flush=True)
    desc = ", ".join(r.rid for r in rows) + "."
    text = HEADER.format(part=f"{part:02d}", desc=desc) + "\n" + "\n".join(body) + \
        "end SignedDifferenceSets.LiftRows\n"
    here = os.path.dirname(os.path.abspath(__file__))
    path = os.path.join(here, "..", "lean", "SignedDifferenceSets", "LiftRows", f"Part{part:02d}.lean")
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(text)
    print("wrote", path)


if __name__ == "__main__":
    main()
