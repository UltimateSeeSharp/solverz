"""All integer Y on small p-groups H with entries in [-B, B] and constant off-peak autocorrelation:
check the Lean form p^min(t, q+1) | sum Y for every allowed e <= v_p(n), r, q (n = 0: e up to 12)."""
import itertools, math, sys
import numpy as np
from rows6 import vp, PAIRS
def elems(ds): return list(itertools.product(*[range(d) for d in ds]))
def run(p, ds, B, chunkdig=11):
    E = elems(ds); v = len(E); idx = {e: i for i, e in enumerate(E)}
    shift = np.array([[idx[tuple((a + b) % d for a, b, d in zip(h, g, ds))] for h in E] for g in E])
    t = vp(v, p); J = vp(max(ds), p)
    rs = [r for r in PAIRS[p] if (r * p) % max(ds) == 0]
    vals = np.arange(-B, B + 1, dtype=np.int64); base = len(vals)
    lo = min(chunkdig, v); hi = v - lo
    low = np.array(list(itertools.product(vals, repeat=lo)), dtype=np.int64)
    cnt = viol = tight = 0
    for top in itertools.product(vals, repeat=hi):
        Y = np.hstack([np.tile(np.array(top, dtype=np.int64), (len(low), 1)), low]) if hi else low
        ac = np.stack([(Y * Y[:, shift[g]]).sum(1) for g in range(v)], 1)
        good = (ac[:, 1:] == ac[:, 1:2]).all(1) if v > 1 else np.ones(len(Y), bool)
        for y, a in zip(Y[good], ac[good]):
            mu = a[1] if v > 1 else 0; n = int(a[0] - mu); s = int(y.sum()); cnt += 1
            emax = 12 if n == 0 else vp(n, p)
            for e in range(emax + 1):
                for r in rs:
                    phi = (p - 1) * r; q = -1
                    while 2 * ((q + 1) * phi + 1) <= e * phi: q += 1
                    if q < 0: continue
                    if s % p ** min(t, q + 1): viol += 1; print('VIOLATION', ds, y, n, mu, e, r, q)
                    elif s % p ** (min(t, q + 1) + 1): tight += 1
    print(f'H={ds} B={B}: {cnt} Y with constant off-peak autocorrelation, {viol} violations, {tight} tight checks', flush=True)
cases = [(2, [2], 4), (2, [4], 3), (2, [2, 2], 3), (2, [8], 2), (2, [2, 4], 2), (2, [2, 2, 2], 2),
         (3, [3], 4), (3, [9], 2), (3, [3, 3], 2), (5, [5], 3), (7, [7], 1), (2, [16], 1), (2, [4, 4], 1),
         (2, [2, 8], 1), (2, [2, 2, 4], 1), (2, [2, 2, 2, 2], 1)]
for p, ds, B in cases[int(sys.argv[1]):int(sys.argv[2])]: run(p, ds, B)
