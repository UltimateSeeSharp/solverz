import math
from kill import kills, parse, rows
for r in rows():
    if r["status"] != "exists": continue
    v, k, lam, fs = parse(r["key"])
    c4 = sum(1 for f in fs if f % 4 == 0)
    if not c4: continue
    n, S = k - lam, k + lam * (v - 1)
    sq = n > 0 and S >= 0 and math.isqrt(n) ** 2 == n and math.isqrt(S) ** 2 == S
    print(r["id"], r["key"], "n=%d S=%d sq=%s" % (n, S, sq))
