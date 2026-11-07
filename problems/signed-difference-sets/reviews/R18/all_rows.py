# Over all rows: (1) exists rows must never be killed, for any exponent-4 quotient order N (any a, b);
# (2) agreement of kill.py with solver/gausschars.py gauss_kills on every (N, m, s) met with N <= 64;
# (3) the open rows killed with N <= 64 and 4 | some d, vs the 297.
import math, sys, re, collections
from kill import PF, kills, parse, rows
sys.path.insert(0, str(PF / "solver")); import gausschars as gc
def orders(fs, cap):
    c4 = sum(1 for f in fs if f % 4 == 0); c2 = sum(1 for f in fs if f % 2 == 0)
    out = set()
    for a in range(0, c4 + 1):
        for b in range(0, c2 - a + 1):
            N = 4 ** a * 2 ** b
            if N <= cap: out.add((N, a, b))
    return out
fired_exists = []; disagree = []; killed_open = {}; seen = {}
for r in rows():
    v, k, lam, fs = parse(r["key"])
    n, S = k - lam, k + lam * (v - 1)
    if n <= 0 or S < 0 or math.isqrt(n) ** 2 != n or math.isqrt(S) ** 2 != S: continue
    m, s = math.isqrt(n), math.isqrt(S)
    cap = 256 if r["status"] == "exists" else 64
    for N, a, b in sorted(orders(fs, cap)):
        key = (N, m, s)
        if key not in seen:
            mine = kills(N, m, s)
            if N <= 64:
                theirs = gc.gauss_kills(N, m, s)
                if mine != theirs: disagree.append((key, mine, theirs))
            seen[key] = mine
        if seen[key]:
            if r["status"] == "exists": fired_exists.append((r["id"], r["key"], N))
            if r["status"] == "open" and a >= 1: killed_open.setdefault(r["id"], N)
print("distinct (N,m,s):", len(seen), "disagreements:", disagree[:10], len(disagree))
print("exists rows fired:", fired_exists)
src = (PF / "lean/SignedDifferenceSets/GaussCharsRows.lean").read_text(encoding="utf-8")
ids = {"N" + x for x in re.findall(r"\(⟨(\d+), \[", src)}
print("open killed (a>=1, N<=64):", len(killed_open), "certs:", len(ids), "certs not killed by me:", ids - set(killed_open))
open("killed_open.txt", "w").write("".join(f"{i}\t{N}\n" for i, N in killed_open.items()))
