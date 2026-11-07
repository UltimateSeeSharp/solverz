"""Lean row theorems for I5's rows above one declaration's budget: E10/E11's `none` rows whose
orbit search (`OrbitSearch.signSearch`) is split at a depth into a top check and slices of its
frontier, one declaration each (`OrbitSearchSplit.lean`); squarefree n through C15
(`not_hasSDS_of_orbitSlices`), other n through C9 for every n (`not_hasSDS_of_orbitSlices'`).

`orbitsplit.py stats <min leaves> <max leaves>`: rows (both kinds) with their search costs.
`orbitsplit.py write-rows <first part> <id>:<m1.m2…>:<k>:<λ> …`: the same for rows given
explicitly (any status, e.g. halved rows that C26 needs, gcd(v, n) = 1), each theorem stated
`¬ @HasSDS (Grp ms) _ inst k λ` for every `inst`.
`orbitsplit.py write <first part> <id> …`: writes the named rows' slices and theorems, in the
order given, into lean/SignedDifferenceSets/OrbitRows/Part<NN>.lean from <first part> on (never
over an existing file), a new part when the next slice would pass PART_CAP; a row's theorem sits
in the part of its last slice, which imports the parts holding its other slices.

`Search` visits exactly the nodes of the Lean search: classes (root, size) in root order, labels
the smallest element of each cycle of y ↦ t·y on Grp ms's numbers (first factor most
significant), signs +, −, 0 in that order, the count test before each class, and at a leaf
whose counts match the shifts' weights in root order until one misses λ. Standard library
only; Lean rechecks everything.
"""
import math
import sys
from pathlib import Path

from orbitrows import OUT_DIR, generator, leaves, orbit_sizes, rows, squarefree

# Node equivalents (≈ 0.45 ms of kernel time each, as a7rows.py), calibrated on N363 with one
# declaration at a time (scratch/agentX/calib3.out): ~100 µs and ~12 KB per weight term at a
# leaf (r² per shift tried), nodes nearly free, a few seconds of setup per declaration (labels,
# weights, frontier). NODE_CAP keeps a slice near 150k weight terms (~20 s, ~2.5 GB).
NODE_CAP = 38_000      # node equivalents per declaration
PART_CAP = 1_000_000   # node equivalents per part file (~8 min)
LEAF_TERM = 0.22       # node equivalents per weight term
NODE_EQ = 0.02         # node equivalents per search node
SETUP = 5_000          # node equivalents per declaration before its search


def digits(x, ms):
    out = []
    for m in reversed(ms):
        out.append(x % m)
        x //= m
    return out[::-1]


def number(dg, ms):
    x = 0
    for a, m in zip(dg, ms):
        x = x * m + a
    return x


class Search:
    """`OrbitSearch.signSearch` on the row, node for node."""

    def __init__(self, ms, k, lam, t, s):
        v = math.prod(ms)
        sc = [number([a * t % m for a, m in zip(digits(y, ms), ms)], ms) for y in range(v)]
        lab = [-1] * v
        for x in range(v):
            if lab[x] < 0:
                lab[x], y = x, sc[x]
                while y != x:
                    lab[y], y = x, sc[y]
        self.roots = [y for y in range(v) if lab[y] == y]
        size = {c: 0 for c in self.roots}
        for y in range(v):
            size[lab[y]] += 1
        self.cls = [(c, size[c]) for c in self.roots]
        pos = {c: i for i, c in enumerate(self.roots)}
        add = lambda y, g: number([(a + b) % m for a, b, m in
                                   zip(digits(y, ms), digits(g, ms), ms)], ms)
        self.Ws = []
        for g in self.roots:
            if g == 0:
                continue
            W = [[0] * len(self.roots) for _ in self.roots]
            for y in range(v):
                W[pos[lab[y]]][pos[lab[add(y, g)]]] += 1
            self.Ws.append(W)
        self.lam, self.r = lam, len(self.roots)
        self.P = max((k + s) // 2, 0)
        self.M = max(k - self.P, 0)
        # reach[i]: the (p, m) some signs on classes i, … reach.
        self.reach = [None] * (self.r + 1)
        self.reach[self.r] = {(0, 0)}
        for i in range(self.r - 1, -1, -1):
            z = self.cls[i][1]
            nxt = self.reach[i + 1]
            self.reach[i] = nxt | {(p + z, m) for p, m in nxt} | {(p, m + z) for p, m in nxt}

    def corr(self, W, sl):
        return sum(a * sum(w * b for w, b in zip(row, sl)) for row, a in zip(W, sl))

    def passes(self, i, p, m):
        """The count test at a node with classes i, … left."""
        return p <= self.P and m <= self.M and (self.P - p, self.M - m) in self.reach[i]

    def run(self, node, st):
        """signSearch from node = (i, pre, p, m); st: nodes, matched leaves, weight terms."""
        i, pre, p, m = node
        st[0] += 1
        if i == self.r:
            if (p, m) != (self.P, self.M):
                return True
            st[1] += 1
            for W in self.Ws:
                st[2] += self.r * self.r
                if self.corr(W, pre) != self.lam:
                    return True
            return False
        if not self.passes(i, p, m):
            return True
        z = self.cls[i][1]
        ok = True
        for ch in ((i + 1, pre + [1], p + z, m), (i + 1, pre + [-1], p, m + z),
                   (i + 1, pre + [0], p, m)):
            if not self.run(ch, st):
                ok = False
        return ok

    def root(self):
        return (0, [], 0, 0)

    def frontier(self, node, d):
        """`OrbitSearch.signFrontier`: the uncut nodes d levels down, in the search's order."""
        i, pre, p, m = node
        if d == 0 or i == self.r:
            return [node]
        if not self.passes(i, p, m):
            return []
        z = self.cls[i][1]
        out = []
        for ch in ((i + 1, pre + [1], p + z, m), (i + 1, pre + [-1], p, m + z),
                   (i + 1, pre + [0], p, m)):
            out += self.frontier(ch, d - 1)
        return out


def cost(st):
    """Node equivalents of a search: its nodes and its leaves' weight terms."""
    return st[0] * NODE_EQ + st[2] * LEAF_TERM


def split(S, cap=NODE_CAP):
    """Depth and cuts [0, …, len] of the frontier so each slice fits in a declaration; the setup
    and the frontier's own nodes are charged to every slice."""
    for d in range(1, S.r + 1):
        nodes = S.frontier(S.root(), d)
        costs = []
        for nd in nodes:
            st = [0, 0, 0]
            S.run(nd, st)
            costs.append(cost(st))
        over = SETUP + len(nodes) * NODE_EQ
        if max(costs, default=0) + over > cap:
            continue
        cuts, acc = [0], 0.0
        for i, c in enumerate(costs):
            if acc + c + over > cap and i > cuts[-1]:
                cuts.append(i)
                acc = 0.0
            acc += c
        cuts.append(len(nodes))
        return d, cuts, costs
    raise ValueError("no depth splits it")


def all_rows(lo, hi):
    out = []
    for nsq in (False, True):
        for lv, r, nid, shape, k, lam, t, s in rows(lo, hi, nsq):
            out.append(dict(nid=nid, leaves=lv, r=r, ms=shape, k=k, lam=lam, t=t, s=s,
                            sqfree=not nsq))
    return out


def explicit_row(spec):
    """`<id>:<m1.m2…>:<k>:<λ>` as a row: t generates C9's multiplier group, s from C1."""
    nid, shape, k, lam = spec.split(":")
    ms, k, lam = [int(m) for m in shape.split(".")], int(k), int(lam)
    v, n = math.prod(ms), k - lam
    s = math.isqrt(k + lam * (v - 1))
    if n <= 1 or math.gcd(v, n) != 1 or s * s != k + lam * (v - 1):
        sys.exit(f"{nid}: needs n > 1 prime to v and k + λ(v − 1) a square")
    t = generator(ms, n)
    sizes = orbit_sizes(ms, t)
    return dict(nid=nid, leaves=leaves(tuple(sizes), (k + s) // 2, (k - s) // 2), r=len(sizes),
                ms=ms, k=k, lam=lam, t=t, s=s, sqfree=squarefree(n), inst=True)


def measure(row):
    S = Search(row["ms"], row["k"], row["lam"], row["t"], row["s"])
    st = [0, 0, 0]
    ok = S.run(S.root(), st)
    if not ok:
        raise ValueError(f"{row['nid']}: a sign choice survives")
    assert S.r == row["r"], row["nid"]
    row.update(search=S, nodes=st[0], matched=st[1], terms=st[2], cost=cost(st))
    return row


def stats_main(lo, hi):
    rs = all_rows(lo, hi)
    for row in rs:
        measure(row)
        print(f"{row['nid']} {'sqf' if row['sqfree'] else 'nsq'} ms={row['ms']} r={row['r']} "
              f"leaves={row['leaves']} nodes={row['nodes']} matched={row['matched']} "
              f"terms={row['terms']} cost={row['cost']:.0f}", flush=True)


def wrap(text, first, rest, width=100):
    lines, cur = [], first
    for w in text.split():
        if len(cur) + len(w) + (cur.strip() != "") > width and cur.strip():
            lines.append(cur)
            cur = rest + w
        else:
            cur = cur + (" " if cur.strip() else "") + w
    lines.append(cur)
    return "\n".join(lines)


def lean_int(x):
    return f"({x})" if x < 0 else str(x)


def lean_list(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


def slice_items(row):
    """The row's slice theorems, each with its cost, and its own theorem (cost: the top)."""
    name, nid = row["nid"].lower(), row["nid"]
    S = row["search"]
    d, cuts, costs = split(S)
    row.update(depth=d, slices=len(cuts) - 1)
    ms, k, lam, t, s = row["ms"], row["k"], lean_int(row["lam"]), row["t"], row["s"]
    data = f"{lean_list(ms)} {k} {lam} {t} {s} {d}"
    items = []
    for i, (a, b) in enumerate(zip(cuts, cuts[1:])):
        items.append((sum(costs[a:b]) + SETUP + len(costs) * NODE_EQ, nid,
                      f"theorem {name}_slice{i} : orbitSlice {data} {a} {b} = true := by\n"
                      f"  decide +kernel\n"))
    grp = " × ".join(f"ZMod {m}" for m in ms)
    rule = "not_hasSDS_of_orbitSlices" if row["sqfree"] else "not_hasSDS_of_orbitSlices'"
    doc = (f"/-- {nid}: {row['r']} orbits of x ↦ {t}x, {row['leaves']} sign choices to evaluate, "
           f"{row['nodes']} nodes; split at depth {d} into {len(cuts) - 1} slices. -/")
    chain = "".join(f"      .cons {name}_slice{i} <|\n" for i in range(len(cuts) - 1))
    stmt = (f"(inst : Fintype (Grp {lean_list(ms)})) :\n"
            f"    ¬ @HasSDS (Grp {lean_list(ms)}) _ inst {k} {lam}"
            if row.get("inst") else f": ¬ HasSDS ({grp}) {k} {lam}")
    items.append((SETUP, None, f"""{wrap(doc, "", "")}
theorem {name}_not_hasSDS {stmt} :=
  {rule} (ms := {lean_list(ms)}) (t := {t}) (s := {s}) (by decide +kernel)
    (orbitExhaust_of_slices (ms := {lean_list(ms)}) (k := {k}) (lam := {lam}) (t := {t})
      (s := {s}) (d := {d})
{wrap(lean_list(cuts[1:]), "      ", "        ")}
      (by decide +kernel) <|
{chain}      .single) {"inst" if row.get("inst") else "_"}
"""))
    return items


def write_main(first, ids, explicit=None):
    """Packs the rows' items in order into parts of at most PART_CAP; a row's theorem goes into
    the part of its last slice, which imports the parts holding its other slices."""
    if explicit is not None:
        table = {row["nid"]: row for row in map(explicit_row, explicit)}
        ids = list(table)
    else:
        table = {row["nid"]: row for row in all_rows(1501, 10 ** 40)}
    missing = [i for i in ids if i not in table]
    if missing:
        sys.exit(f"not open E10/E11 none rows above 1,500 leaves: {missing}")
    parts, cur, acc, where, closing = [], [], 0.0, {}, {}
    for nid in ids:
        row = measure(table[nid])
        for cst, owner, text in slice_items(row):
            if owner is not None and cur and acc + cst > PART_CAP:
                parts.append(cur)
                cur, acc = [], 0.0
            if owner is not None:
                where.setdefault(owner, set()).add(len(parts))
            if owner is None:
                closing[row["nid"]] = len(parts)
            cur.append((row, owner, text))
            acc += cst
    if cur:
        parts.append(cur)
    taken = [first + j for j in range(len(parts))
             if (OUT_DIR / f"Part{first + j:02d}.lean").exists()]
    if taken:
        sys.exit(f"parts {taken} exist; choose another first part")
    for j, part in enumerate(parts):
        num = first + j
        done = [row for row, owner, _ in part if owner is None]
        deps = sorted({i for row in done for i in where[row["nid"]] if i != j})
        imports = (["SignedDifferenceSets.OrbitSearchSplit"]
                   + [f"SignedDifferenceSets.OrbitRows.Part{first + i:02d}" for i in deps])
        body = "\n".join(text for _, _, text in part)
        sq = sum(r["sqfree"] for r in done)
        held = sorted({row["nid"] for row, owner, _ in part if owner is not None}
                      - {r["nid"] for r in done}, key=lambda x: int(x[1:]))
        about = ""
        if done:
            about = (f"{len(done)} open {'row' if len(done) == 1 else 'rows'} "
                     f"({', '.join(r['nid'] for r in done)}) that E10/E11 exhausted, n coprime "
                     f"to v ({sq} with n squarefree, through C15; {len(done) - sq} with n not "
                     f"squarefree, through C9 for every n), each closed by the orbit search split "
                     f"at a depth into slices of its frontier.")
        if held:
            about += (f" Slices of the search for "
                      + ", ".join(f"{h} (closed in part {first + closing[h]:02d})" for h in held)
                      + ".")
        about += " Generated by `solver/orbitsplit.py`."
        title = ("Rows killed by C9 and the orbit search split into slices" if done
                 else "Slices of the orbit search")
        text = f"""module

{chr(10).join(f"public import {m}" for m in imports)}

/-!
# {title}, part {num:02d}

{wrap(about.strip(), "", "")}
-/

@[expose] public section

namespace SignedDifferenceSets.OrbitRows

set_option maxRecDepth 100000
-- One declaration at a time: the slices' kernel checks would otherwise run in parallel and their
-- memory add up.
set_option Elab.async false

{body}
end SignedDifferenceSets.OrbitRows
"""
        (OUT_DIR / f"Part{num:02d}.lean").write_text(text, encoding="utf-8", newline="\n")
        print(f"Part{num:02d}: {len(part)} declarations; rows closed: "
              + ", ".join(f"{r['nid']} ({'sqf' if r['sqfree'] else 'nsq'}, d={r['depth']}, "
                          f"{r['slices']} slices, cost {r['cost']:.0f})" for r in done)
              + (f"; slices of {', '.join(held)}" if held else ""))


if __name__ == "__main__":
    if sys.argv[1] == "stats":
        stats_main(int(sys.argv[2]), int(sys.argv[3]))
    elif sys.argv[1] == "write":
        write_main(int(sys.argv[2]), sys.argv[3:])
    elif sys.argv[1] == "write-rows":
        write_main(int(sys.argv[2]), [], sys.argv[3:])
