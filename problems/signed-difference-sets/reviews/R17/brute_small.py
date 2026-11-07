"""All SDS on every abelian group of order <= 15 (all of {-1,0,1}^G); per (group, k, lam) with an SDS: C17's kill,
C7's generator and C5-family certs must not fire; every SDS with n = k - lam squarefree, gcd(n, v) = 1 has a translate
fixed by every t coprime to v with t = p^f (mod exp G) for all p | n (C15, incl. n = 1)."""
import os, sys, math, itertools
import numpy as np
PF = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(PF, 'solver')); sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import markedcounts as mc, orbitrows as orb
import truth_check as tc

GROUPS = [[2], [3], [4], [2, 2], [5], [6], [7], [8], [2, 4], [2, 2, 2], [9], [3, 3], [10], [11], [12], [2, 6], [13], [14], [15]]
maxv = int(sys.argv[1]) if len(sys.argv) > 1 else 15
for ms in GROUPS:
    v = math.prod(ms)
    if v > maxv or v < (int(sys.argv[2]) if len(sys.argv) > 2 else 0): continue
    elems = list(itertools.product(*[range(m) for m in ms]))
    index = {e: i for i, e in enumerate(elems)}
    def perm(g): return np.array([index[tuple((a + b) % m for a, b, m in zip(e, g, ms))] for e in elems])
    perms = [perm(g) for g in elems[1:]]
    idx = np.arange(3 ** v, dtype=np.int64)
    A = np.empty((3 ** v, v), dtype=np.int8)
    for j in range(v):
        A[:, j] = (idx // 3 ** j) % 3 - 1
    del idx
    A = A[np.any(A != 0, axis=1)]
    c1 = (A.astype(np.int16) * A[:, perms[0]]).sum(axis=1)
    keep = np.ones(len(A), dtype=bool)
    for p in perms[1:]:
        keep &= (A.astype(np.int16) * A[:, p]).sum(axis=1) == c1
    S, lam_all = A[keep], c1[keep]
    del A
    ks = (S != 0).sum(axis=1)
    params = {}
    for row, k, lam in zip(S, ks, lam_all):
        params.setdefault((int(k), int(lam)), []).append(row)
    bad = 0; c15n = 0
    exp = math.lcm(*ms)
    for (k, lam), sets in sorted(params.items()):
        f17 = tc.c17_fires(ms, k, lam)
        if f17: print('!!! C17 fires on existing', ms, k, lam, f17); bad += 1
        c7 = mc.cert(v, k, lam, ms)
        if c7: print('!!! C7 cert on existing', ms, k, lam, c7); bad += 1
        n = k - lam
        if n >= 1 and orb.squarefree(n) and math.gcd(n, v) == 1:
            ps = orb.prime_divisors(n) if n > 1 else []
            ts = [t for t in range(1, exp + 1) if math.gcd(t, v) == 1 and all(any(pow(p, f, exp) == t % exp for f in range(exp)) for p in ps)]
            for row in sets:
                D = {elems[i]: int(row[i]) for i in range(v)}
                ok = any(all(D[tuple((t * x + a) % m for x, a, m in zip(e, aa, ms))] == D[tuple((x + a) % m for x, a, m in zip(e, aa, ms))]
                             for t in ts for e in elems) for aa in elems)
                c15n += 1
                if not ok: print('!!! C15 fails', ms, k, lam, row, ts); bad += 1; break
    print(ms, 'SDS', len(S), 'params', len(params), 'C15-tested sets', c15n, 'violations', bad, flush=True)
