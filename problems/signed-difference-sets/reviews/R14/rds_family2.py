"""As rds_family.py, but translate R-bar so that it misses the coset H (needed when q is odd)."""
import sys
sys.path.insert(0, ".")
from rds_family import field, is_sds

def build(n, p, e):
    q = (n + 1) ** 2
    mod, log = field(p, e)
    N = q * q - 1
    exp = {i: t for t, i in log.items()}
    one = tuple([1] + [0] * (e - 1))
    R = [i for i in range(N)
         if tuple((x + y) % p for x, y in zip(exp[i], exp[(i * q) % N])) == one]
    v = (q + 1) * n
    Rb = sorted({i % v for i in R})
    assert len(Rb) == q
    cosets = {x % (q + 1) for x in Rb}          # H = multiples of q+1 in Z_v
    miss = [c for c in range(q + 1) if c not in cosets]
    assert len(miss) == 1
    D = [0] * v
    for x in Rb:
        D[(x - miss[0]) % v] += 1
    for j in range(n):
        D[(j * (q + 1)) % v] -= 1
    # RDS check: differences of Rb hit H\{0} zero times, every g outside H (q-1)/n times
    c = [0] * v
    for a in Rb:
        for b in Rb:
            c[(a - b) % v] += 1
    rds = all(c[g] == (0 if g % (q + 1) == 0 else (q - 1) // n) for g in range(1, v))
    return v, q + n, n, D, rds

for n, p, e in [(2, 3, 4), (3, 2, 8), (4, 5, 4), (6, 7, 4), (7, 2, 12)]:
    v, k, lam, D, rds = build(n, p, e)
    print((v, k, lam), "RDS:", rds, "SDS:", is_sds(v, k, lam, D), "+", D.count(1), "-", D.count(-1))
    if n == 6:
        open("sds_300_55_6.txt", "w").write("C300 (300,55,6)\n" + "".join(
            f"{x} {'+' if D[x] == 1 else '-'}\n" for x in range(v) if D[x]))
