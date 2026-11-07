"""Brute force of A1's exact claim on small H: every integer a in [-B,B]^H with a a^(-1) = n + mu H
(n > 0, any mu); for each prime p, p not dividing |H|, p self-conjugate mod exp H:
(i) v_p(n) is never odd; (ii) |H| a_h = sigma mod p^b for b = ceil(v_p(n)/2) (p^(2b-1) | n)."""
import sys, itertools, math, ctypes
import numpy as np
sys.path.insert(0, '.')
from xcommon import primefac, self_conj
ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)

def group(shape):
    els = list(itertools.product(*[range(m) for m in shape]))
    idx = {e: i for i, e in enumerate(els)}
    add = np.array([[idx[tuple((x + y) % m for x, y, m in zip(a, b, shape))] for b in els] for a in els])
    return els, add

def run(shape, B):
    els, add = group(shape); h = len(els); m = math.lcm(*shape)
    vals = np.arange(-B, B + 1)
    stats = dict(vec=0, odd=0, tests=0, viol=0, ctrl=0, ctrlviol=0)
    # enumerate in chunks over the first coordinate block
    grid = np.array(list(itertools.product(range(2 * B + 1), repeat=h - 1)), dtype=np.int64) - B if h > 1 else None
    for a0 in range(0, B + 1):                     # a and -a are equivalent; a0 >= 0 suffices? no: keep all, sign-symmetric anyway
        A = np.concatenate([np.full((len(grid), 1), a0), grid], axis=1)
        ac = np.stack([(A * A[:, add[g]]).sum(1) for g in range(h)], axis=1)   # ac[:, g] = sum_x a_x a_{x+g}
        mu = ac[:, 1]
        ok = (ac[:, 1:] == mu[:, None]).all(1)
        n = ac[:, 0] - mu
        ok &= n > 0
        for i in np.nonzero(ok)[0]:
            a = A[i]; nn = int(n[i]); sig = int(a.sum()); stats['vec'] += 1
            for p, e in primefac(nn).items():
                if h % p == 0: continue
                sc = self_conj(p, m)
                b = (e + 1) // 2; q = p ** b
                good = all((h * int(x) - sig) % q == 0 for x in a)
                if sc:
                    stats['tests'] += 1
                    if e % 2: stats['odd'] += 1
                    if not good: stats['viol'] += 1; print('VIOL', shape, a.tolist(), nn, p, e)
                else:
                    stats['ctrl'] += 1; stats['ctrlviol'] += (not good)
    return stats

for shape, B in [((3,), 12), ((4,), 8), ((5,), 6), ((6,), 4), ((7,), 3), ((2, 2), 9), ((8,), 2), ((9,), 2), ((10,), 2), ((3, 3), 2)]:
    print(shape, B, run(shape, B), flush=True)
