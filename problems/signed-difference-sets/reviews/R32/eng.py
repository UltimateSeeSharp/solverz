"""Refuter's independent lift engine (no code from liftrows.py / i16).
Usage: python eng.py ms ds k lam [maxstates]   e.g. 3,3,3 3,3,1 17 4
G = Z_ms (mixed radix, first coordinate most significant), H = Z_ds by coordinatewise reduction.
Phase 1: every b: H -> [-c, c] with sum +s, sum b^2 = k+(c-1)lam, corr_H(u) = c*lam, sum|b| <= k, parity.
Reps under H-translation (canonical = lexicographic min). Phase 2: BFS coset by coset over all
{-1,0,1} patterns with the coset sum, prune by |target(g) - partial corr(g)| <= #pairs not both
assigned and by support bounds; leaves checked exactly. No other symmetry used."""
import sys, itertools, math
import numpy as np

def elems(ms):
    return list(itertools.product(*[range(m) for m in ms]))

def run(ms, ds, k, lam, maxstates=4_000_000, allvecs=False, verbose=True):
    G = elems(ms); v = len(G); gi = {x: i for i, x in enumerate(G)}
    H = elems(ds); n = len(H); hi = {x: i for i, x in enumerate(H)}
    c = v // n
    addG = np.array([[gi[tuple((a + b) % m for a, b, m in zip(x, y, ms))] for y in G] for x in G])
    addH = [[hi[tuple((a + b) % m for a, b, m in zip(x, y, ds))] for y in H] for x in H]
    q = [hi[tuple(a % d for a, d in zip(x, ds))] for x in G]
    s2 = k + lam * (v - 1)
    s = math.isqrt(s2)
    if s * s != s2:
        return ('no s', None)
    Q = k + (c - 1) * lam
    # phase 1
    vecs = []
    b = [0] * n
    def rec(i, sm, sq, ab):
        if sq > Q or ab > k:
            return
        rem = n - i
        if abs(s - sm) > c * rem:
            return
        if i == n:
            if sm != s or sq != Q or (k - ab) % 2:
                return
            for u in range(1, n):
                if sum(b[h] * b[addH[h][u]] for h in range(n)) != c * lam:
                    return
            vecs.append(tuple(b))
            return
        for x in range(-c, c + 1):
            b[i] = x
            rec(i + 1, sm + x, sq + x * x, ab + abs(x))
        b[i] = 0
    rec(0, 0, 0, 0)
    reps = []
    seen = set()
    for w in vecs:
        if w in seen:
            continue
        orb = [tuple(w[addH[h][t]] for h in range(n)) for t in range(n)]
        seen.update(orb)
        reps.append(min(orb))
    todo = vecs if allvecs else reps
    if verbose:
        print(f'v={v} n={n} c={c} s={s} vectors(sum=+s)={len(vecs)} reps={len(reps)}', flush=True)
    # phase 2
    cos = [[x for x in range(v) if q[x] == h] for h in range(n)]
    pats = {}
    for y in range(-c, c + 1):
        pats[y] = np.array([p for p in itertools.product((-1, 0, 1), repeat=c) if sum(p) == y],
                           dtype=np.int8).reshape(-1, c)
    target = np.array([k] + [lam] * (v - 1), dtype=np.int32)
    found = []
    total_nodes = 0
    for w in todo:
        order = sorted(range(n), key=lambda h: (len(pats[w[h]]), h))
        F = np.zeros((1, v), dtype=np.int8)
        assigned = np.zeros(v, dtype=bool)
        minsup = sum(min(int(np.count_nonzero(p)) for p in pats[w[h]]) for h in range(n))
        maxsup = sum(max(int(np.count_nonzero(p)) for p in pats[w[h]]) for h in range(n))
        if not (minsup <= k <= maxsup):
            continue
        remmin, remmax = minsup, maxsup
        for h in order:
            P = pats[w[h]]
            pmin = int(min(np.count_nonzero(p) for p in P)); pmax = int(max(np.count_nonzero(p) for p in P))
            remmin -= pmin; remmax -= pmax
            idx = np.array(cos[h])
            nF = np.repeat(F, len(P), axis=0)
            nF[:, idx] = np.tile(P, (len(F), 1))
            assigned[idx] = True
            total_nodes += len(nF)
            sup = np.count_nonzero(nF, axis=1)
            keep = (sup + remmin <= k) & (sup + remmax >= k)
            nF = nF[keep]
            R = np.array([np.count_nonzero(~(assigned & assigned[addG[:, g]])) for g in range(v)])
            if len(nF):
                Fi = nF.astype(np.int16)
                C = np.empty((len(nF), v), dtype=np.int32)
                for g in range(v):
                    C[:, g] = (Fi * Fi[:, addG[:, g]]).sum(axis=1)
                ok = (np.abs(C - target) <= R).all(axis=1)
                nF = nF[ok]
            F = nF
            if len(F) > maxstates:
                return ('overflow', w)
            if len(F) == 0:
                break
        for f in F:
            fi = f.astype(int)
            ok = all(int((fi * fi[addG[:, g]]).sum()) == (k if g == 0 else lam) for g in range(v))
            if ok:
                found.append((w, tuple(fi)))
        if found and not allvecs:
            break
    return (found, total_nodes, len(vecs), len(reps))

if __name__ == '__main__':
    ms = [int(x) for x in sys.argv[1].split(',')]
    ds = [int(x) for x in sys.argv[2].split(',')]
    k = int(sys.argv[3]); lam = int(sys.argv[4])
    allv = len(sys.argv) > 5 and sys.argv[5] == 'all'
    import time
    t = time.time()
    r = run(ms, ds, k, lam, allvecs=allv)
    if isinstance(r[0], str):
        print('RESULT', r)
    else:
        found, nodes, nv, nr = r
        print(f'RESULT found={len(found)} nodes={nodes} vecs={nv} reps={nr} time={time.time()-t:.1f}s')
        for w, f in found[:3]:
            print('  vec', w, 'f', f)
