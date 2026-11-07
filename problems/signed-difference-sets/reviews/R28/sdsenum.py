"""Exhaustive SDS on Z_m1 x ... (v <= 16) with 4 | n > 0; every such SDS checked on every quotient
Z_2^j x K (qcheck). Prints counts; any violation of (a) or (b) on a 2-self-conjugate K is printed."""
import itertools, math, sys, collections
import numpy as np
from qcheck import elements, run_set

def enum(ms):
    E = elements(ms); v = len(E); idx = {e: i for i, e in enumerate(E)}
    add = np.array([[idx[tuple((a + b) % m for a, b, m in zip(e, g, ms))] for e in E] for g in E])
    lo = min(v, 12); hi = v - lo
    L = np.array(list(itertools.product((-1, 0, 1), repeat=lo)), dtype=np.int8)
    found = []
    for Hh in itertools.product((-1, 0, 1), repeat=hi):
        V = np.concatenate([L, np.tile(np.array(Hh, dtype=np.int8), (len(L), 1))], axis=1) if hi else L
        V16 = V.astype(np.int16)
        ref = (V16 * V16[:, add[1]]).sum(axis=1)
        keep = np.arange(len(V))
        for g in range(2, v):
            a = (V16[keep] * V16[keep][:, add[g]]).sum(axis=1)
            keep = keep[a == ref[keep]]
            if len(keep) == 0: break
        for r in keep:
            D = V[r]; k = int((D != 0).sum()); lam = int(ref[r])
            if k == 0: continue
            found.append((tuple(int(x) for x in D), k, lam))
    return E, found

if __name__ == "__main__":
    for spec in sys.argv[1:]:
        ms = [int(x) for x in spec.split("x")]
        E, found = enum(ms)
        stats = collections.Counter(); viol = []; ctrl = collections.Counter()
        for D, k, lam in found:
            n = k - lam
            if n <= 0 or n % 4: continue
            Dd = {E[i]: s for i, s in enumerate(D) if s}
            for shape, sc, oa, ob, c, forms in run_set(ms, Dd, k, lam, exhaustive_limit=10**9):
                if sc:
                    stats[(oa, ob)] += 1
                    if not (oa and ob): viol.append((D, k, lam, shape, forms, oa, ob))
                else:
                    ctrl[(shape, oa, ob)] += 1
        n4 = sum(1 for D, k, lam in found if k - lam > 0 and (k - lam) % 4 == 0)
        print(spec, "SDS:", len(found), "with 4|n:", n4, "quotient checks (a,b):", dict(stats),
              "violations:", len(viol), "non-selfconj K control:", dict(ctrl), flush=True)
        for x in viol[:5]: print("  VIOL", x)
