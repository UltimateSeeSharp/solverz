"""N3: every function C3xC3 -> {-1,0,1} (3^9), IsSDS checked literally; no symmetry break, no F1."""
import itertools
E = [(a, b) for a in range(3) for b in range(3)]
def add(x, g): return ((x[0] + g[0]) % 3, (x[1] + g[1]) % 3)
idx = {e: i for i, e in enumerate(E)}
shift = {g: [idx[add(x, g)] for x in E] for g in E}
nonzero = [g for g in E if g != (0, 0)]
from collections import Counter
hits = Counter()
for D in itertools.product((-1, 0, 1), repeat=9):
    k = sum(1 for d in D if d)
    corr = tuple(sum(D[i] * D[shift[g][i]] for i in range(9)) for g in nonzero)
    if len(set(corr)) == 1:
        hits[(k, corr[0])] += 1
for key in sorted(hits): print("k,lam", key, "count", hits[key])
print("N3 (8,1):", hits[(8, 1)], " control (8,-1):", hits[(8, -1)])
