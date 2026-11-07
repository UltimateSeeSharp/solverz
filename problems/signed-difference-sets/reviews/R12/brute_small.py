# Exhaustive SDS search on all groups of order <= VMAX (invariant factor lists). For every SDS D
# and every admissible certificate: coset sums are congruent mod q, MomentsOk and BoxOk hold at
# the true (s', t0); for every (G, k, lam) with an SDS, no certificate kills (Kills, BoxKills).
import os, sys, math, itertools
os.environ["OMP_NUM_THREADS"] = "1"
import numpy as np
D0 = r"problems/signed-difference-sets"
sys.path.insert(0, D0 + "/reviews/R12")
from leanmirror import moments_ok, box_ok, kills, box_kills, all_certs, factor
VMAX = int(sys.argv[1])
GROUPS = [[2],[3],[4],[2,2],[5],[6],[7],[8],[2,4],[2,2,2],[9],[3,3],[10],[11],[12],[2,6],[13],[14],[15]]
stats = dict(sds=0, params=0, vec_tests=0, param_tests=0)
for ms in GROUPS:
    v = math.prod(ms)
    if v > VMAX: continue
    els = list(itertools.product(*[range(m) for m in ms])); idx = {e: r for r, e in enumerate(els)}
    add = np.array([[idx[tuple((a + b) % m for a, b, m in zip(x, g, ms))] for x in els] for g in els])
    found = {}  # (k, lam) -> list of D rows
    CH = 3 ** 9
    for start in range(0, 3 ** v, CH):
        num = np.arange(start, min(start + CH, 3 ** v))
        Dm = np.empty((len(num), v), dtype=np.int8); t = num.copy()
        for c in range(v): Dm[:, c] = t % 3 - 1; t //= 3
        k = (Dm != 0).sum(1)
        ac = np.stack([(Dm.astype(np.int16) * Dm[:, add[g]]).sum(1) for g in range(1, v)], 1)
        ok = (ac == ac[:, :1]).all(1) & (k > 0)
        for r in np.nonzero(ok)[0]:
            found.setdefault((int(k[r]), int(ac[r, 0])), []).append(Dm[r].copy())
    for (k, lam), Ds in found.items():
        stats["params"] += 1; stats["sds"] += len(Ds)
        for cert in all_certs(ms, k, lam):
            stats["param_tests"] += 1
            for s in (cert[4], -cert[4]):
                assert not kills(ms, k, lam, *cert[:4], s), (ms, k, lam, cert)
                assert not box_kills(ms, k, lam, *cert[:4], s), (ms, k, lam, cert)
            p, j, i, ds, _ = cert; q = p ** j; h = math.prod(ds); c = v // h
            proj = np.array([sum(((x[t] % ds[t]) * math.prod(ds[t + 1:])) for t in range(len(ms))) for x in els])
            for Dv in Ds:
                a = np.zeros(h, dtype=np.int64); np.add.at(a, proj, Dv.astype(np.int64))
                a = [int(x) for x in a]
                assert all((x - a[0]) % q == 0 for x in a), (ms, k, lam, cert, a)
                sp, Q = sum(a), sum(x * x for x in a)
                assert moments_ok(h, q, sp, Q, a[0] % q) and box_ok(h, q, sp, Q, a[0] % q, c), (ms, k, lam, cert, a)
                stats["vec_tests"] += 1
    print(ms, "params with SDS:", sorted(found), flush=True)
print(stats)
