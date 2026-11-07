"""c = 1 halving test: G with cyclic nontrivial Sylow-2, odd part K (2 self-conjugate mod exp K or not: control),
4 | n > 0. u the element of order 2; E = D + D(. + u) must lie in {0, +-2} and Z = E/2 on G/<u> must be an SDS
(v/2, (k + lam)/4, lam/2)."""
import math, collections, sys
import numpy as np
from qcheck import selfconj2, odd_part

def halve(ms, D, k, lam):
    """D: dict elem -> +-1. Returns (applicable, selfconj, ok, info)."""
    twos = [m & -m for m in ms]
    if sum(1 for t in twos if t > 1) != 1: return False, None, None, None
    ex = math.lcm(*[odd_part(m) for m in ms]); sc = selfconj2(ex)
    t = [i for i, x in enumerate(twos) if x > 1][0]
    A = np.zeros(tuple(ms), dtype=np.int64)
    for e, s in D.items(): A[e] = s
    E = A + np.roll(A, -(ms[t] // 2), axis=t)  # E(x) = D(x) + D(x + u)
    if not np.isin(E, (-2, 0, 2)).all(): return True, sc, False, "E not in {0,+-2}"
    F = np.fft.fftn(E); ac = np.rint(np.real(np.fft.ifftn(F * np.conj(F)))).astype(np.int64)  # sum_x E(x) E(x+g)
    ac = ac / 8  # Z-autocorrelation at the coset of g
    u = [0] * len(ms); u[t] = ms[t] // 2
    want_k, want_l = (k + lam) / 4, lam / 2
    ok = True
    for g in np.ndindex(*ms):
        inP = all(a == 0 for i, a in enumerate(g) if i != t) and g[t] % (ms[t] // 2) == 0
        val = ac[g]
        if inP and val != want_k: ok = False
        if not inP and val != want_l: ok = False
    nz = int((E != 0).sum()) // 2
    return True, sc, ok and nz == want_k, (nz, want_k, want_l)

if __name__ == "__main__":
    from known import sets, verify
    from sdsenum import enum
    st = collections.Counter(); bad = []
    for name, ms, k, lam, D in sets():
        if any(len(e) != len(ms) for e in D) or verify(ms, D) != (k, lam): continue
        if k - lam <= 0 or (k - lam) % 4: continue
        a, sc, ok, info = halve(ms, D, k, lam)
        if not a: continue
        st[("known", sc, ok)] += 1
        if sc and not ok: bad.append((name, info))
        print(name, ms, k, lam, sc, ok, info, flush=True)
    for spec in sys.argv[1:]:
        ms = [int(x) for x in spec.split("x")]
        E_, found = enum(ms)
        for Dv, k, lam in found:
            if k - lam <= 0 or (k - lam) % 4: continue
            D = {E_[i]: s for i, s in enumerate(Dv) if s}
            a, sc, ok, info = halve(ms, D, k, lam)
            if not a: continue
            st[(spec, sc, ok)] += 1
            if sc and not ok: bad.append((spec, Dv, info))
    print(dict(st)); print("violations", len(bad), bad[:5])
