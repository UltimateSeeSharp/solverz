"""(1) Numeric test of (R-H)(R-H)^(-1) = q + (lamR-2)(G-H) + nH for every prime power q <= 64 and every n | q-1,
and of the 'iff'; plus negative controls of the SDS checker and the R+H twin (q=(n-1)^2 -> ordinary DS)."""
import sys, random
from bose import *

def build(q, n):
    p, f = prime_power(q)
    R, _ = bose(q, p, 2 * f)
    v = n * (q + 1)
    Rb = sorted({x % v for x in R})
    assert len(Rb) == q
    lamR = is_rds(Rb, v, q + 1) if n > 1 else q - 1
    assert lamR == (q - 1) // n, (q, n, lamR)
    hit = {x % (q + 1) for x in Rb}
    miss = [c for c in range(q + 1) if c not in hit]
    assert len(miss) == 1
    Rt = [(x - miss[0]) % v for x in Rb]
    assert all(x % (q + 1) for x in Rt)               # misses H, meets every other coset once
    assert len({x % (q + 1) for x in Rt}) == q
    return v, Rt, lamR

bad = 0; rows = 0; sds_cases = []
for q in [3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64]:
    for n in [d for d in range(1, q) if (q - 1) % d == 0]:
        v, Rt, lamR = build(q, n)
        for sign in (-1, +1):
            D = [0] * v
            for x in Rt: D[x] = 1
            for h in range(0, v, q + 1): D[h] = sign
            a = autocorr(D, v)
            # predicted: q + (lamR + 2*sign)(G-H) + nH
            pred = [q + n if g == 0 else (n if g % (q + 1) == 0 else lamR + 2 * sign) for g in range(v)]
            rows += 1
            if a != pred:
                bad += 1; print("MISMATCH", q, n, sign)
            vals = set(a[1:])
            if len(vals) == 1:
                sds_cases.append((sign, q, n, v, q + n, vals.pop()))
print("identity checked on", rows, "(q,n,sign) cases; mismatches:", bad)
print("cases where R -/+ H has constant off-peak correlation:")
for c in sds_cases: print("  sign=%+d q=%d n=%d  (v,k,lam)=(%d,%d,%d)" % c)
# predicted: sign -1: n=1 (any q) or q=(n+1)^2 ; sign +1: n=1 or q=(n-1)^2
for sign, q, n, v, k, lam in sds_cases:
    assert n == 1 or (sign == -1 and q == (n + 1) ** 2) or (sign == 1 and q == (n - 1) ** 2), (sign, q, n)
print("every constant case is n=1 or the predicted q")

# negative controls on the family sets
import json
fam = json.load(open("family_sets.json"))
random.seed(1)
for s, D in fam.items():
    s = int(s); n, q = s - 1, s * s; v, k, lam = len(D), q + n, n
    assert sds_direct(D, v, k, lam)
    rej = 0
    for t in range(20):
        E = D[:]
        i = random.choice([x for x in range(v) if E[x]])
        mode = t % 3
        if mode == 0: E[i] = -E[i]                     # flip a sign
        elif mode == 1 and 0 in E:                      # move an element to an empty spot
            j = random.choice([x for x in range(v) if not E[x]]); E[j] = E[i]; E[i] = 0
        elif mode == 1: E[i] = 0                        # (k = v) drop an element
        ok = sds_direct(E, v, k, lam + 1) if mode == 2 else sds_direct(E, v, k, lam)
        rej += not ok
    print(f"s={s}: {rej}/20 broken variants rejected")
