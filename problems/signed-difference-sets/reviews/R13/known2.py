"""Known sets (rule-sc's gordon_sets, project_sets, constructions) against the Lean statement with
n squarefree: the centroid translate c = alpha * sum a(x) x (alpha s = 1 mod v) must be fixed by every
t in T; C10 on coordinatewise quotients with gcd(|H|, n) = 1. Own checker (brute.py's T_set)."""
import sys, math, itertools, os, collections
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from brute import T_set, sqfree
RSC = "problems/signed-difference-sets/reviews/R4"
sys.path.insert(0, RSC)
import known_sets, constructions

class Gs:
    def __init__(self, shape):
        self.shape = list(shape); self.v = math.prod(shape); self.e = math.lcm(*shape)
        self.I = np.indices(shape).reshape(len(shape), -1)   # coords of flat index
    def flat(self, coords):
        return np.ravel_multi_index(tuple(c % m for c, m in zip(coords, self.shape)), self.shape)

def centroid_fixed(g, a, T):
    s = int(a.sum())
    if math.gcd(abs(s), g.v) != 1: return 'gcd(s,v)>1'
    alpha = pow(s % g.v, -1, g.v) if g.v > 1 else 0
    c = [(alpha * int((a * g.I[j]).sum())) % m for j, m in enumerate(g.shape)]
    b = a[g.flat([g.I[j] + c[j] for j in range(len(g.shape))])]        # b(x) = a(x + c)
    for t in T:
        if not np.array_equal(b[g.flat([t * g.I[j] for j in range(len(g.shape))])], b):
            return f'FAIL t={t}'
    return 'ok'

st = collections.Counter(); bad = []
for src in (known_sets.gordon_sets(), known_sets.project_sets(), constructions.all_sets()):
    for name, shape, k, lam, A in src:
        A = np.asarray(A).reshape(-1).astype(np.int64); shape = list(shape)
        if not known_sets.is_sds(np.asarray(A).reshape(shape), k, lam): st['not_sds'] += 1; continue
        g = Gs(shape); n = k - lam
        if not sqfree(n): st['nonsqf'] += 1; continue
        if math.gcd(g.v, n) == 1:
            T = T_set(g, n); r = centroid_fixed(g, A, T)
            st['C9_' + ('n1' if n == 1 else 'n>1') + ('_T>1' if len(T) > 1 else '_T=1')] += 1
            if r != 'ok': bad.append(('C9', name, shape, k, lam, r))
        for ds in itertools.product(*[[x for x in range(1, m + 1) if m % x == 0] for m in shape]):
            h = math.prod(ds)
            if h == 1 or h == g.v or math.gcd(h, n) != 1: continue
            hs = [d for d in ds]; hg = Gs(hs)
            a = np.zeros(h, np.int64)
            np.add.at(a, hg.flat([g.I[i] for i in range(len(shape))]), A)
            T = T_set(hg, n)
            if len(T) == 1: continue
            st['C10'] += 1
            r = centroid_fixed(hg, a, T)
            if r != 'ok': bad.append(('C10', name, shape, ds, r))
print(dict(st)); print('bad', bad[:20], len(bad))
