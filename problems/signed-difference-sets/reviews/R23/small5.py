"""Every SDS in every abelian group of order <= 12 (all 3^v sign vectors), plus C16 with k >= 15
(lambda >= -1 forces it when k - lambda = 16): my C21 rule must fire on none of the (group, k, lambda) found,
and must fire on some tested (group, k, lambda) with no SDS (so the test is not empty)."""
import os, itertools, numpy as np
os.environ.setdefault('OMP_NUM_THREADS', '2')
exec(open('reviews/R23/rows5.py', encoding='utf-8').read().split('rows = list(')[0].replace('ROOT = sys.argv[1]', 'ROOT = os.getcwd()'))
def groups(v):
    out = []
    def rec(rem, last, acc):  # invariant factors m1 | m2 | ... with product v
        if rem == 1: out.append(acc); return
        for d in range(2, rem + 1):
            if rem % d == 0 and (last is None or d % last == 0): rec(rem // d, d, acc + [d])
    rec(v, None, [])
    return out
def run(ms, kmin=0):
    v = int(np.prod(ms)); els = list(itertools.product(*[range(m) for m in ms]))
    idx = {e: i for i, e in enumerate(els)}
    perms = [np.array([idx[tuple((x[t] + g[t]) % ms[t] for t in range(len(ms)))] for x in els]) for g in els[1:]]
    found = set(); fires = set()
    for k in range(max(kmin, 1), v + 1):
        for supp in itertools.combinations(range(v), k):
            pass
            break
    # enumerate vectors: all sign patterns over supports of size >= kmin, in chunks by support
    from itertools import combinations
    for k in range(max(kmin, 1), v + 1):
        signs = np.array(list(itertools.product([1, -1], repeat=k)), dtype=np.int8)
        signs = signs[signs[:, 0] == 1]  # D and -D give the same (k, lambda)
        for supp in combinations(range(v), k):
            D = np.zeros((len(signs), v), dtype=np.int16); D[:, list(supp)] = signs
            ac = np.stack([(D * D[:, p]).sum(1) for p in perms], 1)
            ok = (ac == ac[:, :1]).all(1)
            for lam in set(ac[ok, 0].tolist()): found.add((k, lam))
    return found
res = []
tested = 0; fired_none = 0
for v in range(2, 13):
    for ms in groups(v):
        f = run(ms)
        for (k, lam) in f:
            assert not best(v, k, lam, ms), ('RULE FIRES ON AN SDS', ms, k, lam)
        nf = [(k, lam) for k in range(1, v + 1) for lam in range(-1, k + 1) if (k, lam) not in f and best(v, k, lam, ms)]
        fired_none += len(nf); tested += 1
        print(ms, 'SDS params:', sorted(f), '| rule fires on (no SDS):', nf, flush=True)
f = run([16], kmin=15)
assert not any(best(16, k, lam, [16]) for (k, lam) in f)
print([16], 'k>=15 SDS params:', sorted(f), '| rule fires on:', [(k, k - 16) for k in (15, 16) if best(16, k, k - 16, [16])])
print('groups', tested, 'rule-fired params (all without SDS):', fired_none)
