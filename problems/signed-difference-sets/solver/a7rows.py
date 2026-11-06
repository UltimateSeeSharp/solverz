"""Lean row theorems for A7: open rows killed by C10 (coset sums on a quotient H with
gcd(|H|, n) = 1, fixed by a multiplier t) and the verified coset search (`CosetSearch.lean`).

`a7rows.py stats`: recomputes every kill and prints the counts.
`a7rows.py write <sqfree|other> <first part>`: writes
lean/SignedDifferenceSets/CosetRows/Part<NN>.lean, one theorem per row (squarefree n through C16;
other n for the general C10 once it is in the library).

Reads the exploration's kills (scratch/a7/mc2_*.out, scratch/ideator/mc_*.out, mcb_*.out), keeps
rows still `open` in instances.csv and reruns each kill with `search`, which visits exactly the
nodes of the Lean search `CosetSearch.valSearch` (same classes, order, cuts and leaf tests). Rows
whose search exceeds NODE_CAP nodes in one declaration are split at a depth into slices of the
search's frontier, each its own declaration. Standard library only; Lean rechecks everything.
"""
import csv
import glob
import math
import re
import sys
from pathlib import Path

from orbitrows import generator, prime_divisors, squarefree

ROOT = Path(__file__).resolve().parent.parent
OUT_DIR = ROOT / "lean" / "SignedDifferenceSets" / "CosetRows"
RUNS = ["scratch/a7/mc2_*.out", "scratch/ideator/mc_*.out", "scratch/ideator/mcb_*.out"]
LINE = re.compile(r"(N\d+) SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\) "
                  r"\('KILL', \(([\d, ]+)\), (\d+), (\d+)\)")
OPEN = "open"
NODE_CAP = 45_000      # node equivalents per declaration (~0.12 MB and ~0.45 ms each)
PART_CAP = 600_000     # node equivalents per part file (~5 min)


def digits(x, ds):
    out = []
    for d in reversed(ds):
        out.append(x % d)
        x //= d
    return out[::-1]


def number(dg, ds):
    x = 0
    for a, d in zip(dg, ds):
        x = x * d + a
    return x


def cycles(ds, t):
    """Labels of the cycles of y ↦ t·y on Grp ds's numbers: each cycle's smallest element
    (`OrbitSearch.scan`); classes (root, size) in root order (`OrbitSearch.classes`)."""
    v = math.prod(ds)
    sc = [number([a * t % d for a, d in zip(digits(y, ds), ds)], ds) for y in range(v)]
    lab = [-1] * v
    for x in range(v):
        if lab[x] >= 0:
            continue
        lab[x], y = x, sc[x]
        while y != x:
            lab[y] = x
            y = sc[y]
    roots = [y for y in range(v) if lab[y] == y]
    size = {c: 0 for c in roots}
    for y in range(v):
        size[lab[y]] += 1
    return lab, roots, [(c, size[c]) for c in roots]


def insertion_sort(cls):
    """Mathlib's `List.insertionSort (fun a b => b.2 ≤ a.2)`: stable, largest class first."""
    out = []
    for a in reversed(cls):
        i = next((i for i, b in enumerate(out) if b[1] <= a[1]), len(out))
        out = out[:i] + [a] + out[i:]
    return out


def max_marked(c, x):
    return c if (c - x) % 2 == 0 else c - 1


def ndist(a, b):
    return abs(a - b)


def mm_n(C, u):
    """`CosetSearch.mmN`: maxMarked C (u − C) in ℕ."""
    return C if u % 2 == 0 else max(C - 1, 0)


def span_n(C, ST, z, rem, su):
    """`CosetSearch.spanN`: the shifted values lo, …, lo + m − 1 tried on a class of size z."""
    if z == 0:
        return 0, 2 * C + 1
    a = max(max(ST - su, 0) - 2 * C * max(rem - z, 0), 0)
    lo = (a + z - 1) // z
    hi = min(2 * C, max(ST - su, 0) // z)
    return lo, max(hi + 1 - lo, 0)


def keep_n(C, QN, ST, z, rem, su, sq, u):
    """`CosetSearch.keepN` (Nat semantics: truncated subtraction)."""
    su2, sq2, R = su + z * u, sq + z * ndist(C, u) ** 2, max(rem - z, 0)
    return (sq2 <= QN and su2 <= ST and ST <= su2 + 2 * C * R
            and ndist(C * R, max(ST - su2, 0)) ** 2 <= R * max(QN - sq2, 0))


class Search:
    """`CosetSearch.valSearch` on the row's quotient, node for node: values x are kept shifted,
    u = x + c in [0, 2c]; QN = k + λ(c − 1), ST = s + c v."""

    def __init__(self, ds, c, k, lam, t, s):
        v = math.prod(ds)
        lab, roots, cls = cycles(ds, t)
        self.cls = insertion_sort(cls)
        rs = [r for r, _ in self.cls]
        pos = {r: i for i, r in enumerate(rs)}
        addg = lambda y, g: number([(a + b) % d for a, b, d in zip(digits(y, ds), digits(g, ds), ds)], ds)
        self.Ws = []
        for g in roots:
            if g == 0:
                continue
            W = [[0] * len(rs) for _ in rs]
            for y in range(v):
                W[pos[lab[y]]][pos[lab[addg(y, g)]]] += 1
            self.Ws.append(W)
        self.c, self.T, self.k = c, lam * c, k
        self.QN, self.ST = max(k + lam * (c - 1), 0), max(s + c * v, 0)
        self.r = len(rs)

    def corr(self, W, sl):
        return sum(a * sum(w * b for w, b in zip(row, sl)) for row, a in zip(W, sl))

    def children(self, node):
        i, rem, pre, su, sq, ab, mm = node
        z, C = self.cls[i][1], self.c
        lo, m = span_n(C, self.ST, z, rem, su)
        for u in range(lo, lo + m):
            if keep_n(C, self.QN, self.ST, z, rem, su, sq, u):
                d = ndist(C, u)
                yield (i + 1, max(rem - z, 0), pre + [u], su + z * u, sq + z * d * d, ab + z * d,
                       mm + z * mm_n(C, u))
            else:
                yield None

    def run(self, node, stats):
        """valSearch from `node` = (i, rem, pre, su, sq, ab, mm); True when every leaf is killed."""
        i, rem, pre, su, sq, ab, mm = node
        stats[0] += 1
        if i == self.r:
            k = self.k
            if not (su == self.ST and sq == self.QN and ab <= k and k <= mm and (k - ab) % 2 == 0):
                return True
            stats[2] += 1
            xs = [u - self.c for u in pre]
            return any(self.corr(W, xs) != self.T for W in self.Ws)
        ok = True
        for ch in self.children(node):
            stats[1] += 1
            if ch is not None and not self.run(ch, stats):
                ok = False
        return ok

    def root(self):
        return (0, sum(z for _, z in self.cls), [], 0, 0, 0, 0)

    def frontier(self, node, d):
        """`CosetSearch.frontier`: the uncut nodes d levels down, in the search's order."""
        if d == 0 or node[0] == self.r:
            return [node]
        return [n for ch in self.children(node) if ch is not None for n in self.frontier(ch, d - 1)]


def kills():
    """The killed rows still open, keyed as in instances.csv (a key that differs is an error)."""
    table = {r["id"]: r for r in csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8"))}
    status = {i: r["status"] for i, r in table.items()}
    seen = {}
    for pat in RUNS:
        for path in sorted(glob.glob(str(ROOT / pat))):
            for line in open(path, encoding="utf-8"):
                m = LINE.fullmatch(line.strip())
                if not m or status.get(m.group(1)) != OPEN or m.group(1) in seen:
                    continue
                nid, v, k, lam, shape, ds, r, nodes = m.groups()
                key = line.split()[1]
                if table[nid]["key"] != key:
                    raise ValueError(f"{nid}: run key {key} != table key {table[nid]['key']}")
                seen[nid] = (nid, int(v), int(k), int(lam), [int(x) for x in shape.split(",")],
                             [int(x) for x in ds.split(",") if x.strip()], int(r), int(nodes))
    return list(seen.values())


def check(row):
    """The row's certificate (t, s, c) and its search, or the reason it fails."""
    nid, v, k, lam, ms, ds, r, nodes = row
    n, o = k - lam, math.prod(ds)
    if n <= 0 or len(ds) != len(ms) or any(m % d for m, d in zip(ms, ds)) or math.gcd(o, n) != 1:
        return None, "bad quotient"
    s = math.isqrt(k + lam * (v - 1))
    if s * s != k + lam * (v - 1):
        return None, "C1 fails"
    t = generator(ds, n)
    if math.gcd(t, o) != 1:
        return None, "t not prime to |H|"
    for p in prime_divisors(n):
        if not any(all(t % d == pow(p, f, d) % d for d in ds) for f in range(o)):
            return None, f"t not a power of {p}"
    S = Search(ds, v // o, k, lam, t, s)
    stats = [0, 0, 0]
    ok = S.run(S.root(), stats)
    if not ok:
        return None, "vector found"
    return dict(nid=nid, v=v, k=k, lam=lam, ms=ms, ds=ds, c=v // o, t=t, s=s, n=n,
                sqfree=squarefree(n), r=S.r, r_run=r, nodes=stats[0], iters=stats[1],
                leaves=stats[2], search=S), "ok"


def cost(stats, r):
    """Node equivalents: nodes, values tried, leaves' correlations (r² terms each)."""
    return stats[0] + stats[1] / 2 + stats[2] * r * r / 20


def split(row):
    """Depth and slice cuts [0, …, len] of the frontier so each slice fits in a declaration."""
    S = row["search"]
    for d in range(1, S.r + 1):
        nodes = S.frontier(S.root(), d)
        costs = []
        for nd in nodes:
            st = [0, 0, 0]
            S.run(nd, st)
            costs.append(cost(st, S.r))
        if max(costs, default=0) > NODE_CAP:
            continue
        cuts, acc = [0], 0.0
        for i, cst in enumerate(costs):
            if acc + cst > NODE_CAP and i > cuts[-1]:
                cuts.append(i)
                acc = 0.0
            acc += cst
        cuts.append(len(nodes))
        return d, cuts
    raise ValueError(f"{row['nid']}: no depth splits it")


def stats_main():
    rows = kills()
    print(f"{len(rows)} kills of rows still open")
    good, bad = [], {}
    for row in rows:
        res, why = check(row)
        if res is None:
            bad[why] = bad.get(why, 0) + 1
            print("FAIL", row[0], why)
        else:
            good.append(res)
    print("failures", bad)
    sq = [g for g in good if g["sqfree"]]
    print(f"recomputed {len(good)}: squarefree n {len(sq)}, other {len(good) - len(sq)}")
    print("r differs from the run's:", sum(g["r"] != g["r_run"] for g in good))
    big = [g for g in good if cost([g["nodes"], g["iters"], g["leaves"]], g["r"]) > NODE_CAP]
    print("need a split:", len(big), [(g["nid"], g["nodes"], g["iters"]) for g in big][:20])
    for key in ("nodes", "iters", "leaves"):
        xs = sorted(g[key] for g in good)
        print(key, "max", xs[-1], "median", xs[len(xs) // 2], "sum", sum(xs))
    vs = sorted(math.prod(g["ds"]) for g in good)
    print("|H| max", vs[-1], "median", vs[len(vs) // 2], "c max", max(g["c"] for g in good))


def wrap(text, first, rest, width=100):
    """`text` as lines of at most `width` characters: `first` before line 1, `rest` before others."""
    lines, cur = [], first
    for w in text.split():
        if len(cur) + len(w) + (cur.strip() != "") > width and cur.strip():
            lines.append(cur)
            cur = rest + w
        else:
            cur = cur + (" " if cur.strip() else "") + w
    lines.append(cur)
    return chr(10).join(lines)


def lean_int(x):
    return f"({x})" if x < 0 else str(x)


def lean_list(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


def theorem(g, general):
    """The row's theorem (and its slices' theorems when it needs a split)."""
    nid, name = g["nid"], g["nid"].lower()
    grp = " × ".join(f"ZMod {m}" for m in g["ms"])
    args = (f"(ms := {lean_list(g['ms'])}) (ds := {lean_list(g['ds'])}) (c := {g['c']}) "
            f"(t := {g['t']}) (s := {g['s']})")
    data = f"{lean_list(g['ds'])} {g['c']} {g['k']} {lean_int(g['lam'])} {g['t']} {g['s']}"
    rule = "not_hasSDS_of_cosetRow'" if general else "not_hasSDS_of_cosetRow"
    hyps = "(by decide +kernel)" if general else "(by decide +kernel) (by decide +kernel)"
    hgrp = " × ".join(f"ZMod {d}" for d in g["ds"])
    doc = (f"{nid}: H = {hgrp} (c = {g['c']}), x ↦ {g['t']}x, "
           f"{g['r']} classes, {g['nodes']} nodes")
    out = []
    if cost([g["nodes"], g["iters"], g["leaves"]], g["r"]) <= NODE_CAP:
        out.append(f"""{wrap(f"/-- {doc}. -/", "", "")}
theorem {name}_not_hasSDS : ¬ HasSDS ({grp}) {g['k']} {lean_int(g['lam'])} :=
  {rule} {args}
    {hyps} (by decide +kernel) _
""")
        return out
    d, cuts = split(g)
    for i, (a, b) in enumerate(zip(cuts, cuts[1:])):
        out.append(f"""theorem {name}_slice{i} : cosetSlice {data} {d} {a} {b} = true := by
  decide +kernel
""")
    chain = "".join(f"      .cons {name}_slice{i} <|{chr(10)}"
                    for i in range(len(cuts) - 1))
    head = wrap(f"/-- {doc}; split at depth {d} into {len(cuts) - 1} slices. -/", "", "")
    out.append(f"""{head}
theorem {name}_not_hasSDS : ¬ HasSDS ({grp}) {g['k']} {lean_int(g['lam'])} :=
  {rule} {args}
    {hyps}
    (cosetSearch_of_slices (ds := {lean_list(g['ds'])}) (c := {g['c']}) (k := {g['k']})
      (lam := {g['lam']}) (t := {g['t']}) (s := {g['s']}) (d := {d})
{wrap(lean_list(cuts[1:]), "      ", "        ")}
      (by decide +kernel) <|
{chain}      .single) _
""")
    return out


def write(kind, first):
    general = kind == "other"
    if not general:
        for old in OUT_DIR.glob("Part*.lean"):
            old.unlink()
    good = []
    for row in kills():
        res, why = check(row)
        if res is None:
            raise ValueError(f"{row[0]}: {why}")
        if res["sqfree"] != general:
            good.append(res)
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
    OUT_DIR.mkdir(exist_ok=True)
    module = "CosetSearchWitt" if general else "CosetSearch"
    via = ("C10 for every n (`not_hasSDS_of_cosetRow'`)" if general
           else "C16 for squarefree n (`not_hasSDS_of_cosetRow`)")
    for j, part in enumerate(parts):
        num = first + j
        body = chr(10).join(t for g in part for t in theorem(g, general))
        text = f"""module

public import SignedDifferenceSets.{module}

/-!
# Rows killed by coset sums fixed by a multiplier (A7), part {num:02d}

{wrap(f"{len(part)} open rows ({part[0]['nid']} to {part[-1]['nid']} in search order), each closed by "
       f"{via} and the coset search on a quotient of order prime to n (generated by "
       f"`solver/a7rows.py`).", "", "")}
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
        stats_main()
    elif sys.argv[1] == "write":
        write(sys.argv[2], int(sys.argv[3]))
