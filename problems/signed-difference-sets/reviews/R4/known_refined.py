# On every verified known set: h a_h = s mod p^j on each qualifying quotient (R1's step), and
# refined.verdict (R1, R2) never kills the set's parameters.
import sys, math, itertools, collections, numpy as np
sys.path.insert(0, ".")
import known_sets as K, constructions, refined
from indep import factor, selfconj
st, bad = collections.Counter(), []
for src in (K.gordon_sets(), K.project_sets(), constructions.all_sets()):
    for name, shape, k, lam, A in src:
        if not K.is_sds(A, k, lam): continue
        v, n, s = math.prod(shape), k - lam, int(A.sum()); st["sets"] += 1
        if refined.verdict(v, k, lam, shape, 2) not in (None,): bad.append(("KILL", name, refined.verdict(v, k, lam, shape, 2)))
        idx = np.indices(shape).reshape(len(shape), -1)
        for d in itertools.product(*[[x for x in range(1, m + 1) if m % x == 0] for m in shape]):
            h = math.prod(d)
            if h == 1 or n <= 0: continue
            a = np.zeros(d, dtype=np.int64); np.add.at(a, tuple(idx[i] % d[i] for i in range(len(shape))), A.reshape(-1))
            for p, e in factor(n).items():
                if e < 2 or h % p == 0 or not selfconj(p, math.lcm(*d)): continue
                q = p ** (e // 2); st["tests"] += 1
                if ((h * a - s) % q != 0).any(): bad.append(("R1STEP", name, d, p))
print(dict(st), "problems:", bad[:10], len(bad))
