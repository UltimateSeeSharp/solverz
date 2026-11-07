"""(2) Build the family for s = n+1 in {2,3,4,5,7,8,9}; check Bose RDS, projection, R - H as SDS (direct + DFT)."""
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0] if "/" in __file__ else ".")
from bose import *

out = {}
for s in [2, 3, 4, 5, 7, 8, 9]:
    p, e = prime_power(s)
    n, q = s - 1, s * s
    R, tail = bose(q, p, 4 * e)
    N = q * q - 1
    big = is_rds(R, N, q + 1)                      # GF(q)* = multiples of q+1
    v = n * (q + 1)
    Rb = sorted({x % v for x in R})
    lamR = is_rds(Rb, v, q + 1) if n > 1 else "n/a"
    hit = {x % (q + 1) for x in Rb}
    miss = [c for c in range(q + 1) if c not in hit]
    D = [0] * v
    for x in Rb:
        D[(x - miss[0]) % v] += 1
    H = list(range(0, v, q + 1))
    for h in H:
        D[h] -= 1
    k, lam = q + n, n
    ok = sds_direct(D, v, k, lam)
    err = sds_dft(D, v, k, lam)
    print(f"s={s} n={n} q={q} poly_tail={tail} |R|={len(R)} bigRDS(q+1,q-1,q,1) lam={big} "
          f"proj distinct={len(Rb)==q} RDS lam={lamR} (want {(q-1)//n}) missed={miss} "
          f"(v,k,lam)=({v},{k},{lam}) SDS direct={ok} DFT err={err:.1e} +{D.count(1)} -{D.count(-1)}", flush=True)
    out[s] = D
import json
json.dump({str(s): D for s, D in out.items()}, open("family_sets.json", "w"))
