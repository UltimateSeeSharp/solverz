# N79/N80 (b): exhaustive search of the SDS (27,22,9) itself on C3^3 and C3 x C9, no contraction.
# sum D = +-16 forces (up to negation) 19 plus, 3 minus, 5 zeros: D = 1_G - 2*1_M - 1_Z.
# For chi != 1: chi(D) = -2 chi(M) - chi(Z); SDS iff |2 chi(M) + chi(Z)|^2 = 13 for all chi != 1.
# Translate so that 0 is in M. Survivors re-checked by integer autocorrelation.
import itertools, numpy as np, sys
def run(ms, k=22, lam=9, nminus=3, nzero=5):
    elems = list(itertools.product(*[range(m) for m in ms])); v = len(elems)
    idx = {e: i for i, e in enumerate(elems)}
    # characters: chi_u(g) = exp(2 pi i sum u_j g_j / m_j)
    ph = np.array([[sum(u[j] * g[j] / ms[j] for j in range(len(ms))) for g in elems] for u in elems])
    X = np.exp(2j * np.pi * ph)            # X[u, g]
    n = k - lam
    zs = list(itertools.combinations(range(v), nzero))
    Zind = np.zeros((len(zs), v), dtype=np.float64)
    for r, z in enumerate(zs): Zind[r, list(z)] = 1
    chiZ = Zind @ X.T                      # (#Z, v)
    found = []
    for rest in itertools.combinations(range(1, v), nminus - 1):
        M = (0,) + rest
        chiM = X[:, list(M)].sum(axis=1)   # (v,)
        ok = ~Zind[:, list(M)].any(axis=1)
        val = np.abs(2 * chiM[None, 1:] + chiZ[:, 1:]) ** 2
        good = ok & np.all(np.abs(val - n) < 1e-6, axis=1)
        for r in np.nonzero(good)[0]:
            D = [1] * v
            for g in M: D[g] = -1
            for g in zs[r]: D[g] = 0
            add = lambda a, b: idx[tuple((x + y) % m for x, y, m in zip(elems[a], elems[b], ms))]
            ac = [sum(D[h] * D[add(h, g)] for h in range(v)) for g in range(1, v)]
            found.append((M, zs[r], set(ac)))
    return found
if __name__ == "__main__":
    # control: (9,8,-1) on C3 x C3: sum = 0 impossible with this split; use (13? no) -> control on C3^2 with
    # k=8, lam=-1: s=0, plus-minus = 0, plus+minus = 8: 4 minus, 1 zero.
    c = run([3, 3], k=8, lam=-1, nminus=4, nzero=1)
    print("control (9,8,-1) on C3xC3:", len(c), "found (with 0 in M)", c[:2])
    for ms in ([3, 3, 3], [3, 9], [27]):
        f = run(ms)
        print("(27,22,9) on", ms, ":", len(f), f[:3]); sys.stdout.flush()
