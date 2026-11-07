# Independent recompute of the rows C22's p = 2 equality kills (own parser, own rule).
import csv, re, sys, math
from math import isqrt
from collections import Counter
BASE = sys.argv[1] if len(sys.argv) > 1 else "instances.csv"
KEY = re.compile(r"^SDS\((-?\d+),(-?\d+),(-?\d+),\[([\d,]*)\]\)$")

def v2(x):
    x = abs(x); c = 0
    if x == 0: return None
    while x % 2 == 0: x //= 2; c += 1
    return c

def rule(v, k, lam, ms, cap_exp):
    """Return (m, w, t, s, ds) if the p = 2 equality kills; cap_exp = max 2-exponent (log2) of a factor."""
    n = k - lam
    if n <= 0: return None
    m = isqrt(n)
    if m * m != n: return None
    S = k + lam * (v - 1)
    if S < 0: return None
    s = isqrt(S)
    if s * s != S: return None
    ds = []
    for mi in ms:
        e = v2(mi)
        ds.append(2 ** min(e, cap_exp))
    t = sum(v2(d) for d in ds)
    w = v2(m)
    if w < t and s % (2 ** (w + 1)) == 0:
        return (m, w, t, s, ds)
    return None

rows = []
with open(BASE, newline="", encoding="utf-8") as f:
    for r in csv.DictReader(f):
        g = KEY.match(r["key"])
        assert g, r["key"]
        v, k, lam = int(g[1]), int(g[2]), int(g[3])
        ms = [int(x) for x in g[4].split(",")] if g[4] else []
        assert math.prod(ms) == v, r["key"]
        rows.append((r["id"], v, k, lam, ms, r["status"], r["evidence"]))

status = Counter(x[5] for x in rows)
print("rows", len(rows), dict(status))
full = {}; lean = {}
for (i, v, k, lam, ms, st, ev) in rows:
    a = rule(v, k, lam, ms, 99)       # stated C22: full Sylow 2-quotient
    b = rule(v, k, lam, ms, 8)        # Lean form: factors | 2r, r <= 128
    if a: full[i] = (a, st, ev, v, k, lam, ms)
    if b: lean[i] = (b, st, ev, v, k, lam, ms)
print("stated-C22 hits by status", Counter(x[1] for x in full.values()))
print("lean-form hits by status", Counter(x[1] for x in lean.values()))
print("lean-only", set(lean) - set(full), "full-only", len(set(full) - set(lean)))
for i, x in full.items():
    if x[1] == "exists": print("EXISTS HIT", i, x)
with open("my_open_hits.txt", "w") as f:
    for i, x in lean.items():
        if x[1] == "open":
            (m, w, t, s, ds) = x[0]
            f.write(f"{i}\t{x[3]}\t{x[4]}\t{x[5]}\t{x[6]}\tm={m} w={w} t={t} s={s} ds={ds}\n")
with open("my_all_hits.txt", "w") as f:
    for i, x in full.items():
        f.write(f"{i}\t{x[1]}\t{x[2]}\t{x[3]}\t{x[4]}\t{x[5]}\t{x[6]}\t{x[0]}\n")
