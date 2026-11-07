"""All D: G -> {-1,0,1} on every abelian group of order <= 13; collect realised (v,k,lam)
(constant autocorrelation over g != 0) and test C1 and C8 (Lean nat semantics) on each D."""
import itertools, math, sys
import numpy as np
from check_rows import sp_lean, is_sq

GROUPS = [[1], [2], [3], [4], [2, 2], [5], [6], [7], [8], [2, 4], [2, 2, 2], [9], [3, 3],
          [10], [11], [12], [2, 6], [13]]
for ms in GROUPS:
    els = list(itertools.product(*[range(m) for m in ms]))
    v = len(els)
    idx = {e: i for i, e in enumerate(els)}
    shifts = [[idx[tuple((a + b) % m for a, b, m in zip(x, g, ms))] for x in els] for g in els[1:]]
    found = {}
    viol = []
    total = 3 ** v
    B = 3 ** min(v, 10)
    for start in range(0, total, B):
        n = np.arange(start, min(start + B, total), dtype=np.int64)
        D = np.empty((len(n), v), dtype=np.int8)
        t = n.copy()
        for j in range(v):
            D[:, j] = (t % 3) - 1; t //= 3
        Di = D.astype(np.int32)
        k = (D != 0).sum(1)
        if v == 1:
            for kk in set(k.tolist()):
                found[(kk, "any")] = 1
            continue
        A = np.stack([(Di * Di[:, s]).sum(1) for s in shifts], 1)
        const = (A == A[:, :1]).all(1)
        for r in np.nonzero(const)[0]:
            lam = int(A[r, 0]); kk = int(k[r]); S = int(Di[r].sum())
            found[(kk, lam)] = found.get((kk, lam), 0) + 1
            if S * S != kk + lam * (v - 1):
                viol.append(("C1", kk, lam, D[r].tolist()))
            if sp_lean(v, kk, lam):
                viol.append(("C8", kk, lam, D[r].tolist()))
    c8_cases = sorted(p for p in found if p[1] != "any" and v % 2 and p[1] % 2 == 0)
    print(ms, "v", v, "realised (k,lam):", len(found), "violations:", viol[:3], len(viol),
          "odd-v even-lam realised:", c8_cases)
    sys.stdout.flush()
