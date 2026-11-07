# SDS verification by pair differences and exact Eisenstein character sums on G/3G.
import math, itertools, collections
from kill20 import kills, traces
def is_sds(ms, D, lam):
    c = collections.Counter()
    pts = list(D.items())
    for x, dx in pts:
        for y, dy in pts:
            g = tuple((b - a) % m for a, b, m in zip(x, y, ms))
            c[g] += dx * dy
    zero = tuple(0 for _ in ms)
    return all(c.get(g, 0) == lam for g in itertools.product(*[range(m) for m in ms]) if g != zero) if math.prod(ms) <= 5000 \
        else all(val == lam for g, val in c.items() if g != zero) and len(c) == math.prod(ms)
def eis_check(ms, D, k, lam):
    """Return (#violations, list of a where C20 fires, details)."""
    v = math.prod(ms); n = k - lam; S = k + lam * (v - 1); s = math.isqrt(S) if S >= 0 else None
    sp = sum(D.values()); viol = []
    if s is None or s * s != S or abs(sp) != s: viol.append(("C1", S, sp))
    idx = [i for i, m in enumerate(ms) if m % 3 == 0]; r = len(idx)
    # psi_c(x) = w^(sum c_i x_i mod 3); value as (A, B) for A + B w; w^2 = -1 - w
    val = {}
    for c in itertools.product(range(3), repeat=r):
        A = B = 0
        for x, d in D.items():
            e = sum(ci * x[i] for ci, i in zip(c, idx)) % 3
            if e == 0: A += d
            elif e == 1: B += d
            else: A -= d; B -= d
        val[c] = (A, B)
    for c, (A, B) in val.items():
        if any(c) and A * A - A * B + B * B != n: viol.append(("norm", c, A, B))
        nc = tuple((-ci) % 3 for ci in c); A2, B2 = val[nc]
        if (A2, B2) != (A - B, -B): viol.append(("conj", c))
        if any(c) and nc == c: viol.append(("real", c))
        if 2 * A - B not in traces(n) and any(c): viol.append(("trace", c))
    fired = []
    for a in range(1, r + 1):
        for sub in itertools.combinations(range(r), a):
            # quotient onto the coordinates `sub`: characters supported on sub; a0 = D over kernel
            a0 = sum(d for x, d in D.items() if all(x[idx[j]] % 3 == 0 for j in sub))
            chars = [c for c in val if all(c[j] == 0 for j in range(r) if j not in sub)]
            tot = sum(2 * val[c][0] - val[c][1] for c in chars)
            if tot != 2 * (3 ** a) * a0: viol.append(("inv", sub, tot, a0))
            ps = sum(2 * val[c][0] - val[c][1] for c in chars if any(c)) // 2
            if sp + ps != 3 ** a * a0: viol.append(("pairsum", sub))
        if s is not None and kills(3 ** a, s, n): fired.append(a)
    return viol, fired, r
