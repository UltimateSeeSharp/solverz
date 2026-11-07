# The rule on every `exists` row: how close it comes (regime) and whether r = R + 1 would fire.
import csv, math, sys, collections
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent)); from rows import parse, v2
PF = Path(__file__).resolve().parents[3]
reg = collections.Counter(); ctrl = []
for row in csv.DictReader(open(PF / "instances.csv", encoding="utf-8")):
    if row["status"] != "exists": continue
    v, k, lam, fs = parse(row["key"]); R = sum(f % 2 == 0 for f in fs)
    if R == 0: continue
    n, S = k - lam, k + lam * (v - 1); s, m = math.isqrt(S), math.isqrt(n)
    assert s * s == S and m * m == n, row["key"]
    a, b = v2(s, 99), v2(m, 99)
    assert min(a, R) == min(b, R), row
    reg["equal below R" if min(a, b) < R else "both >= R"] += 1
    if min(a, R + 1) != min(b, R + 1): ctrl.append((row["id"], row["key"], a, b))
print("exists rows with R>=1:", sum(reg.values()), dict(reg))
print("would die at r=R+1 (control):", len(ctrl), ctrl[:8])
