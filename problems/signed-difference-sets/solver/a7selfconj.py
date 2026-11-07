"""Lean row theorems for I18: A7's coset search with a multiplier t from C25's larger group M′.

`a7selfconj.py stats <targets.tsv>`: checks every target row and prints its certificate or why it fails.
`a7selfconj.py write <targets.tsv> <first part>`: writes lean/SignedDifferenceSets/CosetRows/Part<NN>.lean
(refuses to overwrite), one theorem per killed row through `not_hasSDS_of_cosetRowSelfConj`.
`a7selfconj.py write-congr <targets.tsv> <first part>`: the same through `not_hasSDS_of_cosetRowCongr`, with
C5's congruence mod q = p^j as a filter (`FSearch`, node for node `CosetSearch.valSearchR`), one search per
residue.

`targets.tsv`: lines `<id>\t<d1,d2,…>` (the quotient Grp ds of the row's Grp ms). A prime p ∣ n is in S₂ when
p^i ≡ −1 on every d for some 0 < i < |H| and v_p(n) is even (`CosetRowSelfConj`), else in S₁; t ranges over
M′ = {t prime to |H| : t ≡ p^f on every d for each p ∈ S₁}, and the given t or the one with the fewest classes is used. The search
is a7rows.py's `Search`, node for node the Lean `CosetSearch.valSearch`. Lean rechecks everything.
"""
import csv
import math
import re
import sys

from a7rows import (NODE_CAP, OUT_DIR, PART_CAP, ROOT, Search, cost, cycles, lean_int, lean_list, span_n,
                    split, wrap)
from orbitrows import prime_divisors

KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
OPEN = "open"


def valuation(n, p):
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def self_conj_even(p, n, ds):
    """`CosetRowSelfConj`'s S₂ test: p^i + 1 ≡ 0 on every d for some 0 < i < |H|, and v_p(n) even."""
    o = math.prod(ds)
    conj = any(all((pow(p, i, d) + 1) % d == 0 for d in ds) for i in range(1, o))
    return conj and valuation(n, p) % 2 == 0


def is_power(t, p, ds):
    o = math.prod(ds)
    return any(all(t % d == pow(p, f, d) % d for d in ds) for f in range(o))


def candidates(ds, n):
    """M′ as numbers below lcm(ds), with S₁ and S₂."""
    e, o = math.lcm(*ds), math.prod(ds)
    ps = prime_divisors(n)
    s2 = [p for p in ps if self_conj_even(p, n, ds)]
    s1 = [p for p in ps if p not in s2]
    ts = [t for t in range(1, max(e, 2)) if math.gcd(t, o) == 1 and all(is_power(t, p, ds) for p in s1)]
    return ts, s1, s2


def check(nid, row, ds, t=None):
    v, k, lam, ms = row
    n, o = k - lam, math.prod(ds)
    if n <= 0 or len(ds) != len(ms) or any(m % d for m, d in zip(ms, ds)) or math.gcd(o, n) != 1:
        return None, "bad quotient"
    s = math.isqrt(k + lam * (v - 1))
    if s * s != k + lam * (v - 1):
        return None, "C1 fails"
    ts, s1, s2 = candidates(ds, n)
    if not s2:
        return None, "no self-conjugate prime"
    if t is None:
        t = min(ts, key=lambda t: (len(cycles(ds, t)[1]), t))
    elif t not in ts:
        return None, f"t = {t} not in M′"
    S = Search(ds, v // o, k, lam, t, s)
    stats = [0, 0, 0]
    if not S.run(S.root(), stats):
        return None, f"vector found (t = {t}, {S.r} classes)"
    return dict(nid=nid, v=v, k=k, lam=lam, ms=ms, ds=ds, c=v // o, t=t, s=s, n=n, s1=s1, s2=s2,
                r=S.r, nodes=stats[0], iters=stats[1], leaves=stats[2], search=S), "ok"


def load(path):
    table = {r["id"]: r for r in csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8"))}
    out = []
    for line in open(path, encoding="utf-8"):
        if not line.strip():
            continue
        nid, ds, *t = line.split()
        r = table[nid]
        if r["status"] != OPEN:
            print("SKIP", nid, r["status"])
            continue
        v, k, lam, ms = KEY.fullmatch(r["key"]).groups()
        out.append((nid, (int(v), int(k), int(lam), [int(x) for x in ms.split(",")]),
                    [int(x) for x in ds.split(",")], int(t[0]) if t else None))
    return out


def stats_main(path):
    good = []
    for nid, row, ds, t in load(path):
        res, why = check(nid, row, ds, t)
        if res is None:
            print("FAIL", nid, ds, why)
            continue
        good.append(res)
        print(f"OK {nid} ds={ds} t={res['t']} S1={res['s1']} S2={res['s2']} r={res['r']} "
              f"nodes={res['nodes']} iters={res['iters']} leaves={res['leaves']} "
              f"cost={cost([res['nodes'], res['iters'], res['leaves']], res['r']):.0f}")
    print(f"{len(good)} killed")
    return good


def theorem(g):
    """The row's theorem (and its slices' theorems when it needs a split)."""
    nid, name = g["nid"], g["nid"].lower()
    grp = " × ".join(f"ZMod {m}" for m in g["ms"])
    args = (f"(ms := {lean_list(g['ms'])}) (ds := {lean_list(g['ds'])}) (c := {g['c']}) "
            f"(t := {g['t']}) (s := {g['s']})")
    data = f"{lean_list(g['ds'])} {g['c']} {g['k']} {lean_int(g['lam'])} {g['t']} {g['s']}"
    rule = "not_hasSDS_of_cosetRowSelfConj"
    hgrp = " × ".join(f"ZMod {d}" for d in g["ds"])
    doc = (f"{nid}: H = {hgrp} (c = {g['c']}), x ↦ {g['t']}x, self-conjugate {g['s2']}, "
           f"{g['r']} classes, {g['nodes']} nodes")
    if cost([g["nodes"], g["iters"], g["leaves"]], g["r"]) <= NODE_CAP:
        return [f"""{wrap(f"/-- {doc}. -/", "", "")}
theorem {name}_not_hasSDS : ¬ HasSDS ({grp}) {g['k']} {lean_int(g['lam'])} :=
  {rule} {args}
    (by decide +kernel) (by decide +kernel) _
"""]
    out = []
    d, cuts = split(g)
    for i, (a, b) in enumerate(zip(cuts, cuts[1:])):
        out.append(f"""theorem {name}_slice{i} : cosetSlice {data} {d} {a} {b} = true := by
  decide +kernel
""")
    chain = "".join(f"      .cons {name}_slice{i} <|{chr(10)}" for i in range(len(cuts) - 1))
    head = wrap(f"/-- {doc}; split at depth {d} into {len(cuts) - 1} slices. -/", "", "")
    out.append(f"""{head}
theorem {name}_not_hasSDS : ¬ HasSDS ({grp}) {g['k']} {lean_int(g['lam'])} :=
  {rule} {args}
    (by decide +kernel)
    (cosetSearch_of_slices (ds := {lean_list(g['ds'])}) (c := {g['c']}) (k := {g['k']})
      (lam := {g['lam']}) (t := {g['t']}) (s := {g['s']}) (d := {d})
{wrap(lean_list(cuts[1:]), "      ", "        ")}
      (by decide +kernel) <|
{chain}      .single) _
""")
    return out


def write(path, first):
    good = [g for g in (check(nid, row, ds, t)[0] for nid, row, ds, t in load(path)) if g is not None]
    good.sort(key=lambda g: (cost([g["nodes"], g["iters"], g["leaves"]], g["r"]), int(g["nid"][1:])))
    parts, cur, acc = [], [], 0.0
    for g in good:
        cst = cost([g["nodes"], g["iters"], g["leaves"]], g["r"])
        if cur and acc + cst > PART_CAP:
            parts.append(cur)
            cur, acc = [], 0.0
        cur.append(g)
        acc += cst
    if cur:
        parts.append(cur)
    for j in range(len(parts)):
        if (OUT_DIR / f"Part{first + j:02d}.lean").exists():
            raise FileExistsError(f"Part{first + j:02d}.lean exists")
    for j, part in enumerate(parts):
        num = first + j
        body = chr(10).join(t for g in part for t in theorem(g))
        text = f"""module

public import SignedDifferenceSets.CosetSearchSelfConj

/-!
# Rows killed by coset sums fixed by a multiplier of C25's group (I18), part {num:02d}

{wrap(f"{len(part)} open rows ({part[0]['nid']} to {part[-1]['nid']} in search order), each closed by "
       f"C25 (`not_hasSDS_of_cosetRowSelfConj`: self-conjugate primes of n impose nothing on t) and "
       f"the coset search on a quotient of order prime to n (generated by `solver/a7selfconj.py`).", "", "")}
-/

@[expose] public section

namespace SignedDifferenceSets.CosetRows

set_option maxRecDepth 100000

{body}
end SignedDifferenceSets.CosetRows
"""
        (OUT_DIR / f"Part{num:02d}.lean").write_text(text, encoding="utf-8", newline=chr(10))
        print(f"Part{num:02d}: {len(part)} rows, {part[0]['nid']}..{part[-1]['nid']}, "
              f"{sum(g['nodes'] for g in part)} nodes")
    print(f"{len(good)} rows in {len(parts)} parts")


class FSearch(Search):
    """`CosetSearch.valSearchR`: `Search` trying only shifted values u ≡ res (mod q)."""

    def __init__(self, ds, c, k, lam, t, s, q, res):
        super().__init__(ds, c, k, lam, t, s)
        self.q, self.res = q, res

    def children(self, node):
        i, rem, pre, su, sq, ab, mm = node
        lo, m = span_n(self.c, self.ST, self.cls[i][1], rem, su)
        for ch, u in zip(super().children(node), range(lo, lo + m)):
            yield ch if ch is not None and u % self.q == self.res else None


def modulus(n, ds):
    """`CosetRowCongr`'s q = p^j: the largest p^(v_p(n)//2) over primes p ∤ |H| self-conjugate on ds."""
    o = math.prod(ds)
    best = 1
    for p in prime_divisors(n):
        if o % p and any(all((pow(p, i, d) + 1) % d == 0 for d in ds) for i in range(1, o)):
            best = max(best, p ** (valuation(n, p) // 2))
    return best


def check_cert(nid, row, ds, t=None):
    """The certificate (t, s, c) without the search."""
    v, k, lam, ms = row
    n, o = k - lam, math.prod(ds)
    if n <= 0 or len(ds) != len(ms) or any(m % d for m, d in zip(ms, ds)) or math.gcd(o, n) != 1:
        return None, "bad quotient"
    s = math.isqrt(k + lam * (v - 1))
    if s * s != k + lam * (v - 1):
        return None, "C1 fails"
    ts, s1, s2 = candidates(ds, n)
    if not s2:
        return None, "no self-conjugate prime"
    if t is None:
        t = min(ts, key=lambda t: (len(cycles(ds, t)[1]), t))
    elif t not in ts:
        return None, f"t = {t} not in M′"
    return dict(nid=nid, v=v, k=k, lam=lam, ms=ms, ds=ds, c=v // o, t=t, s=s, n=n, s1=s1, s2=s2), "ok"


def check_congr(nid, row, ds, t=None):
    """`check` with C5's congruence filter: one search per residue mod q."""
    base, why = check_cert(nid, row, ds, t)
    if base is None:
        return None, why
    q = modulus(base["n"], ds)
    if q < 2:
        return None, "no congruence"
    res = []
    for r in range(q):
        S = FSearch(ds, base["c"], base["k"], base["lam"], base["t"], base["s"], q, r)
        st = [0, 0, 0]
        if not S.run(S.root(), st):
            return None, f"vector found (res {r})"
        res.append(dict(nid=nid, search=S, nodes=st[0], iters=st[1], leaves=st[2], r=S.r,
                        cost=cost(st, S.r)))
    base.update(q=q, res=res, nodes=sum(x["nodes"] for x in res), iters=sum(x["iters"] for x in res),
                leaves=sum(x["leaves"] for x in res), r=res[0]["r"])
    return base, "ok"


def theorem_congr(g):
    """The row's theorem through `not_hasSDS_of_cosetRowCongr`, with per-residue searches or slices."""
    nid, name, q = g["nid"], g["nid"].lower(), g["q"]
    grp = " × ".join(f"ZMod {m}" for m in g["ms"])
    args = (f"(ms := {lean_list(g['ms'])}) (ds := {lean_list(g['ds'])}) (c := {g['c']}) "
            f"(t := {g['t']}) (s := {g['s']}) (q := {q})")
    data = f"{lean_list(g['ds'])} {g['c']} {g['k']} {lean_int(g['lam'])} {g['t']} {g['s']} {q}"
    hgrp = " × ".join(f"ZMod {d}" for d in g["ds"])
    doc = (f"{nid}: H = {hgrp} (c = {g['c']}), x ↦ {g['t']}x, self-conjugate {g['s2']}, coset sums "
           f"agree mod {q} (C5), {g['r']} classes, {g['nodes']} nodes")
    total = sum(x["cost"] for x in g["res"])
    if total <= NODE_CAP:
        return [f"""{wrap(f"/-- {doc}. -/", "", "")}
theorem {name}_not_hasSDS : ¬ HasSDS ({grp}) {g['k']} {lean_int(g['lam'])} :=
  not_hasSDS_of_cosetRowCongr {args}
    (by decide +kernel) (by decide +kernel) _
"""]
    out = []
    for r, x in enumerate(g["res"]):
        if x["cost"] <= NODE_CAP:
            out.append(f"""theorem {name}_res{r} : cosetSearchR {data} {r} = true := by
  decide +kernel
""")
            continue
        d, cuts = split(x)
        for i, (a, b) in enumerate(zip(cuts, cuts[1:])):
            out.append(f"""theorem {name}_res{r}_slice{i} :
    cosetSliceR {data} {r} {d} {a} {b} = true := by
  decide +kernel
""")
        chain = "".join(f"    .cons {name}_res{r}_slice{i} <|{chr(10)}" for i in range(len(cuts) - 1))
        out.append(f"""theorem {name}_res{r} : cosetSearchR {data} {r} = true :=
  cosetSearchR_of_slices (ds := {lean_list(g['ds'])}) (c := {g['c']}) (k := {g['k']})
    (lam := {g['lam']}) (t := {g['t']}) (s := {g['s']}) (q := {q}) (res := {r}) (d := {d})
{wrap(lean_list(cuts[1:]), "    ", "      ")}
    (by decide +kernel) <|
{chain}    .single
""")
    word = {2: "two", 3: "three"}[q]
    rs = " ".join(f"{name}_res{r}" for r in range(q))
    out.append(f"""{wrap(f"/-- {doc}; one search per residue. -/", "", "")}
theorem {name}_not_hasSDS : ¬ HasSDS ({grp}) {g['k']} {lean_int(g['lam'])} :=
  not_hasSDS_of_cosetRowCongr {args}
    (by decide +kernel) (forall_lt_{word} {rs}) _
""")
    return out


def write_congr(path, first):
    good = []
    for nid, row, ds, t in load(path):
        g, why = check_congr(nid, row, ds, t)
        if g is None:
            raise ValueError(f"{nid}: {why}")
        good.append(g)
    good.sort(key=lambda g: (sum(x["cost"] for x in g["res"]), int(g["nid"][1:])))
    parts, cur, acc = [], [], 0.0
    for g in good:
        cst = sum(x["cost"] for x in g["res"])
        if cur and acc + cst > PART_CAP:
            parts.append(cur)
            cur, acc = [], 0.0
        cur.append(g)
        acc += cst
    if cur:
        parts.append(cur)
    for j in range(len(parts)):
        if (OUT_DIR / f"Part{first + j:02d}.lean").exists():
            raise FileExistsError(f"Part{first + j:02d}.lean exists")
    for j, part in enumerate(parts):
        num = first + j
        body = chr(10).join(t for g in part for t in theorem_congr(g))
        text = f"""module

public import SignedDifferenceSets.CosetSearchCongr

/-!
# Rows killed by C25's coset-sum multipliers with C5's congruence (I18), part {num:02d}

{wrap(f"{len(part)} open rows ({part[0]['nid']} to {part[-1]['nid']} in search order), each closed by "
       f"C25 and C5 (`not_hasSDS_of_cosetRowCongr`: self-conjugate primes of n impose nothing on t, and "
       f"the coset sums agree mod q) and the filtered coset search on a quotient of order prime to n "
       f"(generated by `solver/a7selfconj.py write-congr`).", "", "")}
-/

@[expose] public section

namespace SignedDifferenceSets.CosetRows

set_option maxRecDepth 100000

{body}
end SignedDifferenceSets.CosetRows
"""
        (OUT_DIR / f"Part{num:02d}.lean").write_text(text, encoding="utf-8", newline=chr(10))
        print(f"Part{num:02d}: {len(part)} rows, {part[0]['nid']}..{part[-1]['nid']}, "
              f"{sum(g['nodes'] for g in part)} nodes")
    print(f"{len(good)} rows in {len(parts)} parts")


if __name__ == "__main__":
    if sys.argv[1] == "stats":
        stats_main(sys.argv[2])
    elif sys.argv[1] == "write":
        write(sys.argv[2], int(sys.argv[3]))
    elif sys.argv[1] == "write-congr":
        write_congr(sys.argv[2], int(sys.argv[3]))
