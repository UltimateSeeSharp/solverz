"""Every D in {-1,0,1}^G (all small groups below) with constant off-zero autocorrelation: test the A5 theorem
(gcd(v,n)=1 => an M-fixed translate) and the A7 theorem on every proper quotient with gcd(|H|,n)=1."""
import sys, itertools, math, collections; sys.path.insert(0, '.')
from common import *
from known_test import invariant_translate
import numpy as np
st = collections.Counter(); bad = []
for shape in ([4], [2, 2], [5], [6], [7], [8], [2, 4], [2, 2, 2], [9], [3, 3], [10], [11], [12], [2, 6], [13], [14], [15]):
    v = math.prod(shape); ax = tuple(range(1, len(shape) + 1)); per = collections.Counter()
    head = max(0, v - 12)
    for pre in itertools.product((-1, 0, 1), repeat=head):
        rest = np.array(list(itertools.product((-1, 0, 1), repeat=v - head)), dtype=np.int8)
        D = np.concatenate([np.tile(np.array(pre, dtype=np.int8), (len(rest), 1)), rest], axis=1)
        F = np.fft.fftn(D.reshape((-1,) + tuple(shape)).astype(float), axes=ax)
        ac = np.rint(np.fft.ifftn(np.abs(F) ** 2, axes=ax).real).reshape(len(D), -1).astype(np.int64)
        good = (ac[:, 1:] == ac[:, 1:2]).all(axis=1) & (ac[:, 0] > 0)
        for row, a in zip(D[good], ac[good]):
            k = int(a[0]); lam = int(a[1]); n = k - lam; A = row.astype(np.int64).reshape(shape)
            if n <= 1: continue
            if math.gcd(v, n) == 1:
                M = mult_group(n, math.lcm(*shape))
                if len(M) > 1:
                    g, cen = invariant_translate(A, list(shape), M); per[('A5', k, lam, len(primes_of(n)) > 1)] += 1
                    if g == 0 or cen is False: bad.append(('A5', shape, k, lam, row.tolist()))
            for ds in itertools.product(*[[x for x in range(1, m + 1) if m % x == 0] for m in shape]):
                h = math.prod(ds)
                if h in (1, v) or math.gcd(h, n) != 1: continue
                M = mult_group(n, math.lcm(*ds))
                if len(M) == 1: continue
                a2 = np.zeros(ds, dtype=np.int64); I = np.indices(shape).reshape(len(shape), -1)
                np.add.at(a2, tuple(I[i] % ds[i] for i in range(len(shape))), A.reshape(-1))
                g, cen = invariant_translate(a2, list(ds), M); per[('A7', k, lam, ds)] += 1
                if g == 0 or cen is False: bad.append(('A7', shape, k, lam, ds, row.tolist()))
    print(shape, dict(per), 'violations so far', len(bad), flush=True)
print('violations', bad[:5])
