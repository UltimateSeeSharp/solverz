"""Multiplicative stabilizers, translate-equivalences, RDS test for O38, projections."""
import sys
sys.path.insert(0, ".")
from check import load, OBJ
from math import gcd

def stab(S, v):
    S = set(S)
    return [t for t in range(1, v) if gcd(t, v) == 1 and {x * t % v for x in S} == S]

def diffcount(S, v):
    c = [0] * v
    for a in S:
        for b in S:
            c[(a - b) % v] += 1
    return c

for o in OBJ:
    v, k, lam, D = load(o)
    P = [x for x in range(v) if D[x] == 1]
    N = [x for x in range(v) if D[x] == -1]
    Z = [x for x in range(v) if D[x] == 0]
    sD = [t for t in range(1, v) if gcd(t, v) == 1 and all(D[x * t % v] == D[x] for x in range(v))]
    print(o, (v, k, lam), "|Stab(D)|", len(sD), "Stab(D)", sD[:30])
    print("   |Stab(Z)|", len(stab(Z, v)), "|Stab(N)|", len(stab(N, v)), "|Stab(P)|", len(stab(P, v)))
    # Z cap -Z
    Zs = set(Z)
    print("   |Z|", len(Z), "|Z cap -Z|", len(Zs & {(-x) % v for x in Z}))
    dz = diffcount(Z, v)
    vals = {}
    for g in range(1, v):
        key = ("Z" if g in Zs else ("-Z" if (-g) % v in Zs else "rest"))
        vals.setdefault(key, set()).add(dz[g])
    print("   diff counts of Z by class:", vals)
    # projections onto divisors
    for d in [p for p in range(2, v) if v % p == 0]:
        img = [0] * d
        for x in range(v):
            img[x % d] += D[x]
        print(f"   image mod {d}:", img if d <= 40 else "(len %d)" % d)
