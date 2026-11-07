"""A5 on every 'exists' Instance with gcd(v,n)=1: knapsack count (0 would be a kill = refutation) and,
when small, the FFT test of every leaf (no SDS among them would also be a kill)."""
import sys, math, collections; sys.path.insert(0, '.')
from common import *
from a5_check import suffix_tables, leaves
import numpy as np
def count_only(sizes, k, s):
    W = 2 * k + 1; t = np.zeros((k + 1, W), dtype=object); t[0, k] = 1
    for z in sizes:
        u = t.copy()
        if z <= k:
            u[z:, z:] += t[:k + 1 - z, :W - z]; u[z:, :W - z] += t[:k + 1 - z, z:]
        t = u
    return int(t[k, s + k])
out = collections.Counter()
for i, key, st, v, k, lam, sh in instances():
    if st != 'exists': continue
    n = k - lam
    if math.gcd(v, n) != 1: out['gcd>1'] += 1; continue
    s2 = n + lam * v; s = math.isqrt(s2); assert s * s == s2
    M = mult_group(n, math.lcm(*sh)); lab, r = orbits(sh, M); lab = np.array(lab)
    sizes = np.bincount(lab, minlength=r).tolist()
    if r > 60:
        c = count_only(sizes, k, s); res = 'KILL' if c == 0 else 'big'
    else:
        suf = suffix_tables(sizes, k); c = int(suf[0][k, s + k])
        if c == 0: res = 'KILL'
        elif c > 2_000_000: res = 'big'
        else:
            F = np.stack([np.fft.fftn((lab == j).reshape(sh).astype(float)).ravel() for j in range(r)])
            E = leaves(sizes, k, s, suf); res = 'KILL'
            for b in range(0, len(E), 20000):
                P = np.abs(E[b:b + 20000].astype(float) @ F) ** 2
                if ((np.abs(P[:, 1:] - n) < 0.5).all(axis=1) & (np.abs(P[:, 0] - s2) < 0.5)).any(): res = 'found'; break
    out[res] += 1
    print(i, key, 'r', r, '|M|', len(M), 'cnt', c, res, flush=True)
print(dict(out))
