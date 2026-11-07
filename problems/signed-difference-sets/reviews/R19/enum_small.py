# Exhaustive SDS enumeration on small abelian groups (all D in {-1,0,1}^G with D(0) = +1, which covers every nonzero
# SDS up to translation and sign). For each SDS: Eisenstein identities on G/3G and C20 must not fire.
import sys, itertools, math, collections
import numpy as np
from eis_lib import eis_check
ms = [int(x) for x in sys.argv[1].split(",")]
G = list(itertools.product(*[range(m) for m in ms])); v = len(G); idx = {g: i for i, g in enumerate(G)}
perm = [np.array([idx[tuple((a + b) % m for a, b, m in zip(x, g, ms))] for x in G]) for g in G[1:]]
rest = v - 1; HEAD = max(0, rest - 12)  # enumerate the last 12 free coords as a block, loop over the head
block = np.array(list(itertools.product((-1, 0, 1), repeat=rest - HEAD)), dtype=np.int16)
found = collections.Counter(); viol_tot = 0; fired_tot = []; nsds = 0
for head in itertools.product((-1, 0, 1), repeat=HEAD):
    D = np.empty((len(block), v), dtype=np.int16); D[:, 0] = 1; D[:, 1:1 + HEAD] = head; D[:, 1 + HEAD:] = block
    c = np.stack([(D * D[:, p]).sum(1) for p in perm], 1)
    ok = (c == c[:, :1]).all(1)
    for row, lam in zip(D[ok], c[ok, 0]):
        Dd = {G[i]: int(x) for i, x in enumerate(row) if x}
        k = len(Dd); lam = int(lam); nsds += 1; found[(k, lam)] += 1
        viol, fired, r = eis_check(ms, Dd, k, lam)
        viol_tot += len(viol)
        if fired: fired_tot.append((k, lam, fired))
print(ms, "SDS with D(0)=1:", nsds, "params", sorted(found.items()), "viol", viol_tot, "fired", fired_tot)
