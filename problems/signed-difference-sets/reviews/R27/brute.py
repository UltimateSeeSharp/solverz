"""Refuter A7, check 2d: every SDS on small groups with n > 0 and gcd(v, n) > 1 (the case 220 batch rows use):
on each quotient H with 1 < |H|, gcd(|H|, n) = 1, the coset sums have one translate fixed by every t in M,
and search() finds a vector for each t != 1 in M."""
import itertools, math, sys
import numpy as np
from search import search, elements
def isprime(p): return p > 1 and all(p % q for q in range(2, math.isqrt(p) + 1))
def mgroup(ds, n):
    e = math.lcm(*ds)
    if e == 1: return [1]
    sets = [{pow(p, f, e) for f in range(2 * e)} for p in range(2, n + 1) if n % p == 0 and isprime(p)]
    M = set.intersection(*sets) if sets else set(range(e))
    return sorted(x for x in M if math.gcd(x, e) == 1)
tot = dict(sds=0, cases=0, notfixed=0, killed=0, searched=0)
for ms in [[6], [10], [12], [2, 6], [14], [15], [3, 6]]:
    E = elements(ms); v = len(E); idx = {e: i for i, e in enumerate(E)}
    perms = [np.array([idx[tuple((x + g) % m for x, g, m in zip(e, gg, ms))] for e in E]) for gg in E[1:]]
    pw = 3 ** np.arange(v)
    found = []
    for lo in range(0, 3 ** v, 1 << 20):
        r = np.arange(lo, min(3 ** v, lo + (1 << 20)))
        X = ((r[:, None] // pw[None, :]) % 3 - 1).astype(np.int8)
        C = np.stack([(X * X[:, p]).sum(axis=1, dtype=np.int32) for p in perms], axis=1)
        ok = (C == C[:, :1]).all(axis=1)
        for row, lam in zip(X[ok], C[ok, 0]):
            k = int(np.abs(row).sum()); n = k - int(lam)
            if n > 0 and math.gcd(v, n) > 1: found.append((row.astype(int), k, int(lam)))
    for a, k, lam in found:
        n = k - lam
        for ds in itertools.product(*[[d for d in range(1, m + 1) if m % d == 0] for m in ms]):
            ds = list(ds); H = math.prod(ds)
            if H == 1 or math.gcd(H, n) != 1: continue
            c = v // H; EH = elements(ds); iH = {e: i for i, e in enumerate(EH)}
            cs = np.zeros(H, dtype=int)
            for e in E: cs[iH[tuple(x % d for x, d in zip(e, ds))]] += a[idx[e]]
            M = mgroup(ds, n)
            def fx(b):
                sh = [cs[iH[tuple((x + y) % d for x, y, d in zip(h, b, ds))]] for h in EH]
                return all(sh[iH[tuple((t * x) % d for x, d in zip(h, ds))]] == sh[iH[h]] for t in M for h in EH)
            tot['cases'] += 1
            if not any(fx(b) for b in EH):
                tot['notfixed'] += 1; print('NOT FIXED', ms, k, lam, ds, list(a))
            for t in [t for t in M if t != 1][:2]:
                tot['searched'] += 1
                if search(ds, c, k, lam, t, abs(int(cs.sum())), cap=200000)[0] == 'killed':
                    tot['killed'] += 1; print('KILLED', ms, k, lam, ds, t)
    tot['sds'] += len(found)
    print(ms, 'SDS with n>0, gcd(v,n)>1:', len(found), tot, flush=True)
