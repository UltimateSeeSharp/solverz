"""Integer vectors a with a a^(-1) = n + mu G (entries VALS); else as brute.py: every SDS on small abelian groups (exhaustive over {-1,0,1}^G); for n = k - lam > 0 with gcd(v, n) = 1, test C9:
one translate fixed by every t in M = cap_p <p mod e>. Count non-squarefree n separately. Control: all units."""
import itertools, math, sys
import numpy as np
from math import gcd
def pf(n):
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: out.append(n)
    return out
def sqf(n): return all(n % (p * p) for p in pf(n))
def run(ms):
    els = list(itertools.product(*[range(m) for m in ms])); v = len(els); idx = {x: i for i, x in enumerate(els)}
    add = lambda x, y: tuple((a + b) % m for a, b, m in zip(x, y, ms))
    perms = [np.array([idx[add(x, g)] for x in els]) for g in els[1:]]
    e = math.lcm(*ms)
    smul = lambda t: np.array([idx[tuple((t * a) % m for a, m in zip(x, ms))] for x in els])
    stats = dict(sds=0, applicable=0, nonsqf=0, fail=0, ctrl_fixed=0, ctrl_tested=0)
    vals = np.array(VALS, dtype=np.int8); B = len(VALS)
    total = B ** v; chunk = B ** min(v, 8)
    for start in range(0, total, chunk):
        ids = np.arange(start, min(start + chunk, total), dtype=np.int64)
        D = np.empty((len(ids), v), dtype=np.int8)
        r = ids.copy()
        for j in range(v): D[:, j] = vals[r % B]; r //= B
        D16 = D.astype(np.int16)
        lam = (D16 * D16[:, perms[0]]).sum(1)
        ok = np.ones(len(ids), dtype=bool)
        for p in perms[1:]:
            ok &= (D16 * D16[:, p]).sum(1) == lam
        k = (D16 * D16).sum(1)  # = n + mu, so kk - ll = n
        ok &= (D != 0).sum(1) > 0
        for i in np.nonzero(ok)[0]:
            stats['sds'] += 1
            kk, ll = int(k[i]), int(lam[i]); n = kk - ll
            if n <= 0 or gcd(v, n) != 1: continue
            stats['applicable'] += 1
            ns = not sqf(n); stats['nonsqf'] += ns
            M = [t for t in range(1, e + 1) if gcd(t, e) == 1 and all(any(t % e == pow(p, f, e) for f in range(e)) for p in pf(n))]
            units = [t for t in range(1, e + 1) if gcd(t, e) == 1]
            d = D[i]
            def fixed(ts):
                maps = [smul(t) for t in ts]
                for a in range(v):
                    pa = np.array([idx[add(x, els[a])] for x in els]); da = d[pa]  # da[x] = D(x + a)
                    if all(np.array_equal(da[mp], da) for mp in maps): return True
                return False
            if not fixed(M):
                stats['fail'] += 1; stats['fail'] <= 5 and print('FAIL', ms, kk, ll, d.tolist(), flush=True)
            if ns and len(units) > len(M):
                stats['ctrl_tested'] += 1; stats['ctrl_fixed'] += fixed(units)
    return stats
VALS = [int(x) for x in sys.argv[1].split(',')]
for spec in sys.argv[2:]:
    ms = [int(x) for x in spec.split('x')]
    print(spec, run(ms), flush=True)
