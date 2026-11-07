"""Structure of O34-O38: multiplier invariance, orbits by sign, cyclotomic description."""
import sys
sys.path.insert(0, ".")
from check import load, OBJ
from math import gcd

def primes(n):
    p, out = 2, []
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out

def subgroup(gens, v):
    S = {1}
    frontier = [1]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = x * g % v
            if y not in S:
                S.add(y); frontier.append(y)
    return sorted(S)

def orbits(M, v):
    seen, out = set(), []
    for x in range(v):
        if x not in seen:
            o = sorted({x * m % v for m in M})
            seen |= set(o); out.append(o)
    return out

for o, nid in OBJ.items():
    v, k, lam, D = load(o)
    n = k - lam
    ps = primes(n)
    # E10's M: intersection of <p mod v> over p | n
    sets = [set(subgroup([p % v], v)) for p in ps]
    M = sorted(set.intersection(*sets))
    inv = all(D[x * m % v] == D[x] for m in M for x in range(v))
    # sign classes as unions of orbits
    orb = orbits(M, v)
    by = {1: [], -1: [], 0: []}
    for ob in orb:
        sg = {D[x] for x in ob}
        assert len(sg) == 1 or not inv
        by[D[ob[0]]].append(len(ob))
    print(o, nid, (v, k, lam), "n", n, "primes", ps, "|M|", len(M), "M-invariant", inv,
          "#orbits", len(orb))
    print("   orbit sizes +", sorted(by[1]), " -", sorted(by[-1]), " 0", sorted(by[0]))
    Nset = [x for x in range(v) if D[x] == -1]
    Zset = [x for x in range(v) if D[x] == 0]
    print("   N =", Nset, " zeros(", len(Zset), ") =", Zset if len(Zset) < 40 else Zset[:40])
    # symmetric?
    print("   D(-x)=D(x) for all x:", all(D[(-x) % v] == D[x] for x in range(v)),
          " D(-x)=-D(x)?", all(D[(-x) % v] == -D[x] for x in range(v)))
