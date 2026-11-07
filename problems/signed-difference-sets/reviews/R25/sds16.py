# Part 1: every SDS (every D in {-1,0,1}^G with constant off-zero autocorrelation) on every abelian group of
# order 4, 8, 12, 16; test C22's p = 2 equality (n = m^2; w = v2(m) < t => 2^(w+1) does not divide s) with H the
# Sylow 2-quotient (t = v2(v), the strongest choice) and also the Lean theorem's hypotheses literally.
import itertools, numpy as np, sys
from collections import Counter
def v2(x):
    x = abs(x); c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
def table(ms):
    el = list(itertools.product(*[range(m) for m in ms])); idx = {e: i for i, e in enumerate(el)}
    return [[idx[tuple((a + b) % m for a, b, m in zip(e, f, ms))] for e in el] for f in el]  # add[g][x] = x+g
def run(ms):
    v = int(np.prod(ms)); add = table(ms)
    lo = min(v, 12); hi = v - lo
    L = np.array(list(itertools.product((-1, 0, 1), repeat=lo)), dtype=np.int16)
    stats = Counter(); viol = []; params = Counter()
    for H in itertools.product((-1, 0, 1), repeat=hi):
        V = np.concatenate([L, np.tile(np.array(H, dtype=np.int16), (len(L), 1))], axis=1) if hi else L
        ref = (V * V[:, add[1]]).sum(axis=1)
        keep = np.ones(len(V), bool)
        for g in range(2, v):
            idx = np.nonzero(keep)[0]
            if len(idx) == 0: break
            a = (V[idx] * V[idx][:, add[g]]).sum(axis=1)
            keep[idx[a != ref[idx]]] = False
        for r in np.nonzero(keep)[0]:
            D = V[r]; k = int((D != 0).sum()); lam = int(ref[r]); s = int(D.sum())
            n = k - lam; t = v2(v)
            params[(k, lam)] += 1
            if n <= 0: stats["n<=0"] += 1; continue
            m = int(round(n ** 0.5))
            if m * m != n:
                stats["nonsquare"] += 1
                if t >= 1: viol.append(("nonsquare", ms, k, lam, s))
                continue
            w = v2(m)
            if w < t:
                stats["tested w<t"] += 1
                if s % 2 ** (w + 1) == 0: viol.append(("eq", ms, k, lam, s, D.tolist()))
                if v2(s) == w if s else False: stats["v2(s)=w"] += 1
            else: stats["w>=t"] += 1
    return stats, viol, params
groups = [[4], [2, 2], [8], [2, 4], [2, 2, 2], [12], [2, 6], [16], [4, 4], [2, 8], [2, 2, 4], [2, 2, 2, 2]]
for ms in groups:
    st, vi, pa = run(ms)
    print(ms, dict(st), "violations:", len(vi), vi[:2], "params:", sorted(pa)); sys.stdout.flush()
