"""Independent orbit search (refuter xsplit). Group Z_m1 x ... x Z_mr, multiplier t (componentwise x -> t x),
or the full group M (mode 'M': all t prime to v with t = p^f on every factor, for each prime p | n).
Sign choices on orbits with exactly P = (k+s)/2 plus and Q = (k-s)/2 minus elements (s >= 0, s^2 = k + lam(v-1));
each such leaf checked by batched FFT autocorrelation. Prints leaves, found count."""
import sys, math, time, itertools
import numpy as np
def primes(n):
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: out.append(n)
    return out
def run(ms, k, lam, t, mode, cap, stop_first=False):
    v = math.prod(ms); n = k - lam
    s = math.isqrt(k + lam * (v - 1)); assert s * s == k + lam * (v - 1)
    P, Q = (k + s) // 2, (k - s) // 2; assert P + Q == k
    elems = list(itertools.product(*[range(m) for m in ms]))
    idx = {e: i for i, e in enumerate(elems)}
    if mode == 'M':
        e = math.lcm(*ms)
        Ts = [u for u in range(1, e) if math.gcd(u, v) == 1 and all(any(all(u % m == pow(p, f, m) for m in ms) for f in range(e)) for p in primes(n))]
    else:
        Ts = [t]
    seen = [False] * v; orbs = []
    for x in elems:
        if seen[idx[x]]: continue
        o, frontier = {idx[x]}, [x]
        while frontier:
            y = frontier.pop()
            for u in Ts:
                z = tuple(a * u % m for a, m in zip(y, ms))
                if idx[z] not in o: o.add(idx[z]); frontier.append(z)
        for i in o: seen[i] = True
        orbs.append(sorted(o))
    orbs.sort(key=len, reverse=True)
    sizes = [len(o) for o in orbs]; r = len(orbs)
    reach = [None] * (r + 1); reach[r] = {(0, 0)}
    for i in range(r - 1, -1, -1):
        z = sizes[i]; nx = reach[i + 1]
        reach[i] = {pm for pm in nx} | {(p + z, m) for p, m in nx if p + z <= P} | {(p, m + z) for p, m in nx if m + z <= Q}
    D = np.zeros(v, dtype=np.int8)
    batch, B = [], 4096
    st = dict(leaves=0, found=0, cut=False)
    shape = tuple(ms)
    def flush():
        if not batch: return
        A = np.array(batch, dtype=np.float64).reshape((len(batch),) + shape)
        F = np.fft.fftn(A, axes=tuple(range(1, len(shape) + 1)))
        ac = np.rint(np.real(np.fft.ifftn(F * np.conj(F), axes=tuple(range(1, len(shape) + 1))))).reshape(len(batch), v)
        ok = (ac[:, 0] == k) & np.all(ac[:, 1:] == lam, axis=1)
        st['found'] += int(ok.sum())
        if ok.any() and 'example' not in st: st['example'] = batch[int(np.argmax(ok))].copy()
        batch.clear()
    def go(i, p, m):
        if st['cut'] or (stop_first and st['found']): return
        if i == r:
            if p == P and m == Q:
                st['leaves'] += 1
                batch.append(D.copy())
                if len(batch) >= B: flush()
                if st['leaves'] > cap: st['cut'] = True
            return
        if (P - p, Q - m) not in reach[i]: return
        o = orbs[i]; z = sizes[i]
        D[o] = 1; go(i + 1, p + z, m)
        D[o] = -1; go(i + 1, p, m + z)
        D[o] = 0; go(i + 1, p, m)
    sys.setrecursionlimit(10000)
    go(0, 0, 0); flush()
    return dict(v=v, s=s, P=P, Q=Q, nT=len(Ts), r=r, leaves=st['leaves'], found=st['found'], cut=st['cut'], example=st.get('example'))
if __name__ == '__main__':
    mode, cap = sys.argv[1], int(sys.argv[2])
    for arg in sys.argv[3:]:
        nid, shape, k, lam, t = arg.split(':')
        ms = [int(x) for x in shape.split('.')]
        t0 = time.time()
        R = run(ms, int(k), int(lam), int(t), mode, cap)
        res = 'cut' if R['cut'] else ('FOUND' if R['found'] else 'none')
        print(nid, shape, k, lam, 't=' + t, mode, 'nT=%d r=%d P=%d Q=%d leaves=%d found=%d' % (R['nT'], R['r'], R['P'], R['Q'], R['leaves'], R['found']), res, '%.1fs' % (time.time() - t0), flush=True)
