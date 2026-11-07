"""Every `exists` row meeting C26's c = 1 hypotheses must have a feasible halved row: lam even, 2|s| <= k + lam,
parity, and the halved row (G/P, (k+lam)/4, lam/2) not `none` in the table. Also: every exists row passes C26 on
every quotient (rows_indep.killing empty)."""
import csv, re, math, collections
from pathlib import Path
from rows_indep import factor, selfconj2, killing
from halfrows_check import inv
ROOT = Path(__file__).resolve().parents[3]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
rows = list(csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8")))
bytype = {}
for r in rows:
    v, k, lam, ms = KEY.fullmatch(r["key"]).groups()
    ms = [int(x) for x in ms.split(",")]
    bytype[(tuple(sorted((p, tuple(e)) for p, e in inv(ms).items())), int(k), int(lam))] = r
st = collections.Counter(); bad = []
for r in rows:
    if r["status"] != "exists": continue
    v, k, lam, ms = KEY.fullmatch(r["key"]).groups(); v, k, lam = int(v), int(k), int(lam); ms = [int(x) for x in ms.split(",")]
    if killing(ms, k, lam): bad.append((r["id"], r["key"], "killed by parity")); continue
    n = k - lam
    if n <= 0 or n % 4: continue
    t = inv(ms)
    if len(t.get(2, [])) != 1: continue
    odd = 1
    for p, es in t.items():
        if p != 2: odd = math.lcm(odd, p ** max(es))
    if not selfconj2(odd): continue
    st["c=1 shape"] += 1
    S = k + lam * (v - 1); s = math.isqrt(S)
    if lam % 2 or 2 * s > k + lam: bad.append((r["id"], r["key"], "halved infeasible", s)); continue
    t2 = {p: list(e) for p, e in t.items()}; t2[2] = [t2[2][0] - 1]
    if t2[2] == [0]: del t2[2]
    key2 = (tuple(sorted((p, tuple(e)) for p, e in t2.items())), (k + lam) // 4, lam // 2)
    h = bytype.get(key2)
    st[("halved", h["status"] if h else "off table")] += 1
    if h and h["status"] == "none": bad.append((r["id"], r["key"], "halved row none", h["id"], h["evidence"]))
    print(r["id"], r["key"], "->", h["id"] if h else "-", h["key"] if h else key2, h["status"] if h else "", flush=True)
print(dict(st)); print("bad", bad)
