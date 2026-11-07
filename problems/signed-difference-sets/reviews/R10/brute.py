# (A) eq_zero_of_autocorr exhaustively: every b in F_p^H with all autocorrelations 0 is 0 when
#     exp(H) | p^i + 1; controls (not self-conjugate) must have nonzero solutions.
# (B) congr_pow_of_autocorr: every a in [-B,B]^H with autocorrelation n[g=0] + mu, for each
#     prime p, j = v_p(n)//2 (n = 0: j = 4): a constant mod p^j iff test passes.
import itertools, math, sys, numpy as np, collections
def elems(shape): return list(itertools.product(*[range(m) for m in shape]))
def shift_idx(shape):
    E = elems(shape); ix = {e: t for t, e in enumerate(E)}
    return E, np.array([[ix[tuple((x + g) % m for x, g, m in zip(e, gg, shape))] for e in E] for gg in E])
def selfconj(p, shape):
    e = math.lcm(*shape); x = p % e
    for i in range(1, 2 * e + 2):
        if (x + 1) % e == 0: return i
        x = x * p % e
    return None
def vecs(vals, m, chunk=200000):
    vals = np.array(vals, dtype=np.int64); N = len(vals) ** m
    for s in range(0, N, chunk):
        idx = np.arange(s, min(N, s + chunk)); out = np.empty((len(idx), m), np.int64)
        for c in range(m): out[:, c] = vals[idx % len(vals)]; idx = idx // len(vals)
        yield out
def autocorr(X, S):  # X: (N, m); R[:, g] = sum_h X[h] X[h+g]
    return np.stack([(X * X[:, S[g]]).sum(1) for g in range(S.shape[0])], 1)
res = collections.Counter()
A = [((3,), 2), ((3,), 5), ((5,), 2), ((5,), 3), ((5,), 7), ((4,), 3), ((4,), 7), ((2, 2), 3), ((2, 2), 5),
     ((6,), 5), ((7,), 3), ((7,), 5), ((9,), 2), ((3, 3), 2), ((11,), 2), ((10,), 3), ((2, 4), 3), ((2, 2, 2), 3),
     ((9,), 5), ((3, 3), 5), ((8,), 7),
     ((7,), 2), ((8,), 3), ((3,), 7), ((5,), 11), ((2, 4), 5), ((15,), 2), ((13,), 3)]  # last: controls
for shape, p in A:
    E, S = shift_idx(shape); m = len(E); sc = selfconj(p, shape); nz = 0
    if p ** m > 6e6: continue
    for X in vecs(range(p), m):
        R = autocorr(X, S) % p
        nz += int(((R == 0).all(1) & (X != 0).any(1)).sum())
    print("A", shape, "p", p, "selfconj i =", sc, "nonzero b with zero autocorr:", nz, flush=True)
    res["A", sc is not None, nz > 0] += 1
B = [((3,), 9), ((4,), 6), ((5,), 4), ((2, 2), 6), ((6,), 3), ((7,), 2), ((8,), 2), ((9,), 1), ((3, 3), 1), ((2, 4), 2), ((10,), 1)]
for shape, Bd in B:
    E, S = shift_idx(shape); m = len(E); cnt = collections.Counter(); ex = []
    for X in vecs(range(-Bd, Bd + 1), m):
        R = autocorr(X, S); off = R[:, 1:]
        ok = (off == off[:, :1]).all(1); X, R = X[ok], R[ok]
        for x, r in zip(X, R):
            n = int(r[0] - r[1]); assert n >= 0
            for p in [2, 3, 5, 7, 11, 13]:
                e = 8 if n == 0 else next(t for t in range(64) if (n // p ** t) % p)
                j = e // 2
                if j == 0: continue
                sc = selfconj(p, shape) is not None and math.prod(shape) % p
                const = bool(((x - x[0]) % p ** j == 0).all())
                cnt[bool(sc), const, e % 2 if n else "n0", min(j, 3)] += 1
                if sc and not const and len(ex) < 3: ex.append((list(x), n, p, j))
    print("B", shape, "B", Bd, dict(cnt), "VIOL" if ex else "", ex, flush=True)
