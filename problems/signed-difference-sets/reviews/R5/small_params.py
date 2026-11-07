"""All (k, lam) realised by some D in {-1,0,1}^G for C10, C14, C15 (exhaustive), to test Gordon's
'Orbit Exhaust' No labels with gcd(v,n) > 1 at small v."""
import sys, itertools, math; sys.path.insert(0, '.')
from common import *
import numpy as np
for v in (10, 14, 15):
    found = set(); head = max(0, v - 12)
    for pre in itertools.product((-1, 0, 1), repeat=head):
        rest = np.array(list(itertools.product((-1, 0, 1), repeat=v - head)), dtype=np.int8)
        D = np.concatenate([np.tile(np.array(pre, dtype=np.int8), (len(rest), 1)), rest], axis=1).astype(float)
        F = np.fft.fft(D, axis=1); ac = np.rint(np.fft.ifft(np.abs(F) ** 2, axis=1).real).astype(np.int64)
        good = (ac[:, 1:] == ac[:, 1:2]).all(axis=1) & (ac[:, 0] > 0)
        found |= {(int(a[0]), int(a[1])) for a in ac[good]}
    print(v, sorted(found), flush=True)
