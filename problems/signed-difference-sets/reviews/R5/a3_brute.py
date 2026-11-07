"""Exhaustive: every D in {-1,0,1}^G on small odd groups with constant off-zero autocorrelation lam;
record (v, k, lam) and test A3: lam even => d(d-1) >= v-1. Also the zero-set parity lemma per D."""
import sys, itertools, math; sys.path.insert(0, '.')
from common import *
import numpy as np
for shape in ([3], [5], [7], [9], [3, 3], [11], [13]):
    v = math.prod(shape); found = set(); viol = 0
    for chunk in range(3):
        rest = np.array(list(itertools.product((-1, 0, 1), repeat=v - 1)), dtype=np.int8)
        D = np.concatenate([np.full((len(rest), 1), chunk - 1, dtype=np.int8), rest], axis=1).astype(float)
        F = np.fft.fft2(D.reshape((-1,) + tuple(shape)), axes=tuple(range(1, len(shape) + 1))).reshape(len(D), -1)
        ac = np.rint(np.fft.ifft2((np.abs(F) ** 2).reshape((-1,) + tuple(shape)), axes=tuple(range(1, len(shape) + 1))).real).reshape(len(D), -1).astype(np.int64)
        good = (ac[:, 1:] == ac[:, 1:2]).all(axis=1) & (ac[:, 0] > 0)
        for row, a in zip(D[good], ac[good]):
            k = int(a[0]); lam = int(a[1]); d = v - k; found.add((k, lam))
            if lam % 2 == 0 and d * (d - 1) < v - 1: viol += 1
    print(shape, 'SDS params found', sorted(found), 'A3 violations', viol, flush=True)
