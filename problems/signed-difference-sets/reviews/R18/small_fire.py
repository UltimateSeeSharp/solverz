import math
from kill import kills
def orders(fs):
    c4 = sum(1 for f in fs if f % 4 == 0); c2 = sum(1 for f in fs if f % 2 == 0)
    return sorted({4 ** a * 2 ** b for a in range(1, c4 + 1) for b in range(0, c2 - a + 1)})
groups = [[4], [8], [2, 4], [12], [16], [2, 8], [4, 4], [2, 2, 4], [20], [24], [2, 12], [28], [32], [2, 16], [4, 8], [2, 2, 8], [2, 4, 4], [36], [3, 12]]
for fs in groups:
    v = math.prod(fs); out = []
    for k in range(1, v + 1):
        for lam in range(-k, k + 1):
            n, S = k - lam, k + lam * (v - 1)
            if n <= 0 or S < 0 or math.isqrt(n) ** 2 != n or math.isqrt(S) ** 2 != S: continue
            m, s = math.isqrt(n), math.isqrt(S)
            Ns = [N for N in orders(fs) if kills(N, m, s)]
            if Ns: out.append((k, lam, m, s, Ns))
    print(fs, v, out)
