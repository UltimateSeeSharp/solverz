"""Independent orbit search on cyclic exists rows with n not squarefree, gcd(v,n)=1: t = generator of M (own code),
s = sqrt(k + lam(v-1)); DFS over <t>-orbits with exact +/- counts, autocorrelation check at leaves. found/none/cut."""
import sys, math, time
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
def M_of(v, n):
    return [t for t in range(1, v + 1) if gcd(t, v) == 1 and all(any(t % v == pow(p, f, v) for f in range(v)) for p in pf(n))]
def search(v, k, l, cap):
    n = k - l; s = math.isqrt(k + l * (v - 1)); assert s * s == k + l * (v - 1)
    M = M_of(v, n)
    seen = [False] * v; orbs = []
    for x in range(v):
        if seen[x]: continue
        o = sorted({(t * x) % v for t in M})
        for y in o: seen[y] = True
        orbs.append(o)
    orbs.sort(key=len, reverse=True)
    P, Q = (k + s) // 2, (k - s) // 2
    sizes = [len(o) for o in orbs]
    suf = [0] * (len(sizes) + 1)
    for i in range(len(sizes) - 1, -1, -1): suf[i] = suf[i + 1] + sizes[i]
    D = np.zeros(v); leaves = [0]
    def check():
        F = np.fft.fft(D); ac = np.rint(np.real(np.fft.ifft(F * np.conj(F))))
        return ac[0] == k and np.all(ac[1:] == l)
    def go(i, p, q):
        if leaves[0] > cap: return None
        if p == P and q == Q:
            leaves[0] += 1
            return check()
        if i == len(orbs) or suf[i] < (P - p) + (Q - q): return False
        c = sizes[i]
        for sg, p2, q2 in ((1, p + c, q), (-1, p, q + c), (0, p, q)):
            if p2 <= P and q2 <= Q:
                for y in orbs[i]: D[y] = sg
                r = go(i + 1, p2, q2)
                for y in orbs[i]: D[y] = 0
                if r is None or r: return r
        return False
    r = go(0, 0, 0)
    return ('cut' if r is None else 'found' if r else 'none'), len(M), len(orbs), leaves[0]
for arg in sys.argv[2:]:
    v, k, l = map(int, arg.split(','))
    t0 = time.time()
    print(arg, *search(v, k, l, int(sys.argv[1])), '%.1fs' % (time.time() - t0), flush=True)
