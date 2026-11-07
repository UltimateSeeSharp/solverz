"""Is O38 = (Bose RDS projected, translated) - H up to a multiplier and translate? Is its P an RDS?"""
import sys
sys.path.insert(0, ".")
from math import gcd
from check import load
import rds_family2 as F  # prints its table on import

v, k, lam, D = load("O38")
P = {x for x in range(v) if D[x] == 1}
N = {x for x in range(v) if D[x] == -1}
c = [0] * v
for a in P:
    for b in P:
        c[(a - b) % v] += 1
print("O38: N is subgroup of order 7:", N == {65 * j for j in range(7)},
      " P is (65,7,64,9) RDS rel N:", all(c[g] == (0 if g % 65 == 0 else 9) for g in range(1, v)),
      " P misses N:", not (P & N))
_, _, _, B, _ = F.build(7, 2, 12)
BP = {x for x in range(v) if B[x] == 1}
hits = [(t, g) for t in range(1, v) if gcd(t, v) == 1 for g in range(0, v, 65)
        if {(t * x + g) % v for x in BP} == P]
print("O38 P = t*BoseP + g for (t,g):", hits[:5], "count", len(hits))
