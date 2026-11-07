"""The 11 sets the ideator's orbit search found for open Instances (oe_*.out 'found'), rebuilt
from the orbit signs; verification happens in the caller (FFT autocorrelation)."""
import sys, glob, ast, itertools, math
import numpy as np
SCR = "problems/signed-difference-sets/scratch"
def found_sets():
    sys.path.insert(0, SCR + '/ideator')
    from mult import mult_group
    from load import parse, exponent
    for line in itertools.chain.from_iterable(open(p) for p in glob.glob(SCR + '/ideator/oe_*.out')):
        p = line.split(None, 6)
        if p[3] != 'found': continue
        i, key = p[0], p[1]; eps = ast.literal_eval(p[6].strip())
        v, k, lam, f = parse(key); n = k - lam
        M = mult_group(n, exponent(f))
        A = np.zeros(f, dtype=np.int64); seen = set(); oi = 0
        for g in itertools.product(*[range(m) for m in f]):
            if g in seen: continue
            o = {tuple(t * x % m for x, m in zip(g, f)) for t in M}
            for y in o: A[y] = eps[oi]; seen.add(y)
            oi += 1
        yield f"F:{i}:{key}", list(f), k, lam, A

def found_sets_he():
    """The 2 sets of he_*.out (assumed multipliers M' = intersection of <p mod e>, p | n, p not | e)."""
    sys.path.insert(0, SCR + '/ideator')
    import mult
    from load import parse, exponent, pf
    for line in itertools.chain.from_iterable(open(p) for p in glob.glob(SCR + '/ideator/he_*.out')):
        p = line.split(None, 6)
        if len(p) < 7 or p[3] != 'found': continue
        i, key = p[0], p[1]; eps = ast.literal_eval(p[6].strip())
        v, k, lam, f = parse(key); n = k - lam; e = exponent(f)
        M = None
        for q, _ in pf(n):
            if e % q == 0: continue
            S = mult.cyc_sub(q, e); M = S if M is None else M & S
        M = M or {1}
        A = np.zeros(f, dtype=np.int64); seen = set(); oi = 0
        for g in itertools.product(*[range(m) for m in f]):
            if g in seen: continue
            o = {tuple(t * x % m for x, m in zip(g, f)) for t in M}
            for y in o: A[y] = eps[oi]; seen.add(y)
            oi += 1
        assert oi == len(eps), (key, oi, len(eps))
        yield f"F:{i}:{key}", list(f), k, lam, A
