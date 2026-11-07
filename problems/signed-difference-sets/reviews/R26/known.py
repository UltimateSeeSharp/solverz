"""C9 for every n on known sets: every object O1..O70 with n = k-lam > 0, gcd(v,n)=1 (squarefree or not):
is it an SDS, and is some translate fixed by every t in M = cap_p <p mod exp G>? Also the control: all units."""
import re, math, glob, itertools, sys, os
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
def load(fn):
    L = open(fn).read().split('\n')
    m = re.match(r'(\S+) \((\d+),(\d+),(-?\d+)\)', L[0])
    ms = [int(x) for x in m[1].replace('C', '').split('x')]
    v, k, l = int(m[2]), int(m[3]), int(m[4])
    assert math.prod(ms) == v
    D = np.zeros(ms, dtype=np.int64)
    for line in L[1:]:
        a = line.split()
        if not a: continue
        D[tuple(int(x) for x in a[:-1])] = 1 if a[-1] == '+' else -1
    return ms, v, k, l, D
def is_sds(D, k, l):
    if np.count_nonzero(D) != k: return False
    F = np.fft.fftn(D.astype(float))
    ac = np.rint(np.real(np.fft.ifftn(F * np.conj(F)))).astype(np.int64)
    flat = ac.flatten()
    return flat[0] == k and all(flat[1:] == l)
def scale(D, ms, t):
    """D^(t): x -> D(t^{-1} x) ; we need D(t x) as array: E[x] = D[t x]."""
    idx = np.meshgrid(*[(np.arange(m) * t) % m for m in ms], indexing='ij')
    return D[tuple(idx)]
def fixed_translate(D, ms, ts):
    for a in itertools.product(*[range(m) for m in ms]):
        Da = np.roll(D, shift=[-x for x in a], axis=tuple(range(len(ms))))  # Da[x] = D[x + a]
        if all(np.array_equal(scale(Da, ms, t), Da) for t in ts): return a
    return None
rows = []
for fn in sorted(glob.glob(sys.argv[1] + '/O*.txt'), key=lambda f: int(re.search(r'O(\d+)', f)[1])):
    ms, v, k, l, D = load(fn); n = k - l
    ok = is_sds(D, k, l)
    if not (n > 0 and gcd(v, n) == 1):
        rows.append((fn[-7:], v, k, l, n, ok, 'C9 n/a')); continue
    e = math.lcm(*ms)
    M = [t for t in range(1, e + 1) if gcd(t, e) == 1 and all(any(t % e == pow(p, f, e) for f in range(e)) for p in pf(n))]
    a = fixed_translate(D, ms, M)
    units = [t for t in range(1, e + 1) if gcd(t, e) == 1]
    ctrl = fixed_translate(D, ms, units) if len(units) > len(M) else 'same'
    rows.append((os.path.basename(fn), ms, (v, k, l), 'n=%d' % n, 'sqf' if sqf(n) else 'NONSQF', 'SDS' if ok else 'NOT SDS', '|M|=%d' % len(M), 'fixed at %s' % (a,), 'all-units control: %s' % (ctrl,)))
for r in rows: print(*r)
