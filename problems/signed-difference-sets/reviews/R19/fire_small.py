# All parameter sets (v, k, lam) with s^2 = k + lam(v-1), 1 <= k <= v, |lam| <= k, on which C20 fires at N = 3^a
# for a <= 4, v <= VMAX, 3^a | v (3-rank a needs 3^a | v); parity filter k = s mod 2 noted.
import math, sys
from kill20 import kills, traces
VMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 60
for v in range(3, VMAX + 1, 3):
    for k in range(1, v + 1):
        for lam in range(-k, k + 1):
            S = k + lam * (v - 1)
            if S < 0 or math.isqrt(S) ** 2 != S: continue
            s = math.isqrt(S)
            fa = [a for a in range(1, 5) if v % 3 ** a == 0 and kills(3 ** a, s, k - lam)]
            if fa: print(v, k, lam, "n", k - lam, "s", s, "parity_ok", (k - s) % 2 == 0, "T", sorted(traces(k - lam))[:6], "a", fa)
