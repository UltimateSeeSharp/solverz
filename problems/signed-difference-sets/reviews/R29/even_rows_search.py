"""Independent exhaustive search for C28's halved vector Z on L for the 8 EvenRows (expects none).
L = Z_r x Z_d; Z: |Z|<=c, sum Z^2 = Q, sum Z = +-s2, autocorr t at g != 0, sum|Z| <= K, sum|Z| = K mod 2.
Pruning: sum (Z - mu)^2 = Q - s2^2/|L| (exact, rational) over the remaining entries."""
from fractions import Fraction as Fr
import itertools, sys
rows = {  # id: (v, k, lam, r, d, c, s, K)
    664: (64, 18, 2, 16, 1, 2, 12, 8), 675: (64, 22, 6, 16, 1, 2, 20, 10),
    741: (64, 46, 30, 16, 1, 2, 44, 22), 763: (64, 58, 42, 16, 1, 2, 52, 28),
    4672: (144, 38, 2, 1, 9, 8, 18, 19), 4712: (144, 56, 20, 1, 9, 8, 54, 27),
    4762: (144, 92, 56, 1, 9, 8, 90, 45), 20961: (280, 252, 216, 2, 5, 14, 246, 125)}
def search(v, k, lam, r, d, c, s, K):
    assert s * s == k + lam * (v - 1) and v % (2 * r * d) == 0 and c == v // (2 * r * d)
    Q, t, s2 = Fr(k + lam * (2 * c - 1), 4), Fr(lam * c, 2), s // 2
    assert Q.denominator == 1 and t.denominator == 1
    Q, t = int(Q), int(t)
    N = r * d
    els = [(a, b) for a in range(r) for b in range(d)]
    idx = {e: i for i, e in enumerate(els)}
    add = [[idx[((a + x) % r, (b + y) % d)] for (x, y) in els] for (a, b) in els]
    sols = []
    for S in (s2, -s2):
        mu = Fr(S, N); var = Q - Fr(S * S, N)
        vals = [z for z in range(-c, c + 1) if (z - mu) ** 2 <= var]
        Z = [0] * N
        def rec(i, sm, sq, va):
            if i == N:
                if sm != S or sq != Q: return
                sa = sum(abs(z) for z in Z)
                if sa > K or (K - sa) % 2: return
                for g in range(1, N):
                    if sum(Z[h] * Z[add[h][g]] for h in range(N)) != t: return
                sols.append(list(Z)); return
            rem = N - i
            for z in vals:
                nv = va + (z - mu) ** 2
                if nv > var: continue
                # remaining sum must be reachable: |S - sm - z| <= rem-1 * c ; and sq bound
                if abs(S - sm - z) > (rem - 1) * c or sq + z * z > Q: continue
                Z[i] = z; rec(i + 1, sm + z, sq + z * z, nv)
            Z[i] = 0
        rec(0, 0, 0, Fr(0))
    return Q, t, s2, sols
for i, row in rows.items():
    Q, t, s2, sols = search(*row)
    print(f"N{i}", "Q", Q, "t", t, "s2", s2, "solutions", len(sols), sols[:2], flush=True)
