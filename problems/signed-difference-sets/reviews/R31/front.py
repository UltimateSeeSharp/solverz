"""Lean-order frontier (labels = smallest number in each t-cycle, first factor most significant; classes in root
order; signs +, -, 0; count test) and the index of the node agreeing with a known t-fixed solution."""
import sys, math, itertools
sys.path.insert(0, '.')
from search import run
ms, k, lam, t, d = [int(x) for x in sys.argv[1].split('.')], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
R = run(ms, k, lam, t, 't', 10**8, stop_first=True)
sol = R['example']; assert sol is not None
v = math.prod(ms); P, Q = R['P'], R['Q']
el = list(itertools.product(*[range(m) for m in ms])); num = {e: i for i, e in enumerate(el)}
sc = [num[tuple(a * t % m for a, m in zip(e, ms))] for e in el]
lab = [-1] * v
for x in range(v):
    if lab[x] < 0:
        lab[x], y = x, sc[x]
        while y != x: lab[y], y = x, sc[y]
roots = sorted({lab[x] for x in range(v)}); sz = {c: sum(1 for x in range(v) if lab[x] == c) for c in roots}
cls = [(c, sz[c]) for c in roots]; r = len(cls)
reach = [None] * (r + 1); reach[r] = {(0, 0)}
for i in range(r - 1, -1, -1):
    z = cls[i][1]; reach[i] = reach[i + 1] | {(p + z, m) for p, m in reach[i + 1]} | {(p, m + z) for p, m in reach[i + 1]}
def front(i, pre, p, m, dd):
    if dd == 0 or i == r: return [pre]
    if not (p <= P and m <= Q and (P - p, Q - m) in reach[i]): return []
    z = cls[i][1]
    return front(i + 1, pre + [1], p + z, m, dd - 1) + front(i + 1, pre + [-1], p, m + z, dd - 1) + front(i + 1, pre + [0], p, m, dd - 1)
F = front(0, [], 0, 0, d)
want = [int(sol[c]) for c, _ in cls[:d]]
print('r', r, 'frontier', len(F), 'solution prefix', want, 'index', [i for i, f in enumerate(F) if f == want[:len(f)]])
