"""For the 13 E8-found jobs where A2 rejects every autocorrelation vector in V^h: which A2 bound
fails? E8 enforces sum|a| <= k and parity, so the failing one must be k <= sum maxm."""
import sys, math, itertools, collections
sys.path.insert(0, '.')
import numpy as np
from xrules import maxm
src = open('e8_lemma.py').read()
head = src.split("jobs = sorted(jobs.items())")[0].replace("out, w, nw = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])", "")
ns = {'__file__': 'e8_lemma.py'}; exec(head, ns)
shifts = None
exec(src.split("jobs = sorted(jobs.items())")[1].split("with open(out")[0], ns)
for (fs, V, s, Q, mu, k, c), ids in sorted(ns['jobs'].items()):
    if len(V) > 7: continue
    h = math.prod(fs); add = ns['shifts'](fs); Va = np.array(V)
    A = Va[np.array(list(itertools.product(range(len(V)), repeat=h)))]
    A = A[(A.sum(1) == s) & ((A * A).sum(1) == Q)]
    ok = np.ones(len(A), bool)
    for g in range(1, h): ok &= (A * A[:, add[g]]).sum(1) == mu
    A = A[ok]
    fails = collections.Counter()
    for a in A:
        Aab = int(np.abs(a).sum()); M = sum(maxm(int(x), c) for x in a)
        fails[(Aab <= k, (k - Aab) % 2 == 0, k <= M)] += 1
    if not any(f[0] and f[1] and f[2] for f in fails): print(ids[:3], fs, V, 'k', k, 'c', c, 'vectors', len(A), '(abs<=k, parity, k<=sum maxm):', dict(fails))
