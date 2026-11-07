"""Lemma test on integer vectors: every Y on H = Z_N x Z_d1 x ... (N = 2^j first) with entries in [-R, R] and
Y Y^(-1) = n + m H (all off-identity autocorrelations equal m), 4 | n: (a) 2 | Y(h+u) - Y(h), u = (N/2, 0..);
(b) 8 | 2 sum Y - n - 2m. Usage: ytest.py R spec... (spec like 4x3)."""
import itertools, sys, collections
import numpy as np
from qcheck import elements, selfconj2

def run(ms, R):
    E = elements(ms); v = len(E); idx = {e: i for i, e in enumerate(E)}
    add = np.array([[idx[tuple((a + b) % m for a, b, m in zip(e, g, ms))] for e in E] for g in E])
    N = ms[0]; u = idx[tuple([N // 2] + [0] * (len(ms) - 1))]
    vals = tuple(range(-R, R + 1)); base = len(vals)
    lo = v
    while base ** lo > 600000: lo -= 1
    hi = v - lo
    L = np.array(list(itertools.product(vals, repeat=lo)), dtype=np.int16)
    st = collections.Counter(); ex = []
    for Hh in itertools.product(vals, repeat=hi):
        V = np.concatenate([L, np.tile(np.array(Hh, dtype=np.int16), (len(L), 1))], axis=1) if hi else L
        ref = (V * V[:, add[1]]).sum(axis=1)
        keep = np.arange(len(V))
        for g in range(2, v):
            a = (V[keep] * V[keep][:, add[g]]).sum(axis=1)
            keep = keep[a == ref[keep]]
            if len(keep) == 0: break
        if len(keep) == 0: continue
        Vk = V[keep]; m = ref[keep].astype(np.int64)
        a0 = (Vk.astype(np.int64) ** 2).sum(axis=1); n = a0 - m
        sel = (n > 0) & (n % 4 == 0)
        Vk, m, n = Vk[sel], m[sel], n[sel]
        if len(Vk) == 0: continue
        oka = ((Vk - Vk[:, add[u]]) % 2 == 0).all(axis=1)
        okb = (2 * Vk.astype(np.int64).sum(axis=1) - n - 2 * m) % 8 == 0
        for x, y in zip(oka, okb): st[(bool(x), bool(y))] += 1
        bad = np.nonzero(~(oka & okb))[0]
        for b in bad[:3]: ex.append((Vk[b].tolist(), int(n[b]), int(m[b])))
    return st, ex

if __name__ == "__main__":
    R = int(sys.argv[1])
    for spec in sys.argv[2:]:
        ms = [int(x) for x in spec.split("x")]
        sc = all(selfconj2(d) for d in ms[1:])
        st, ex = run(ms, R)
        print(spec, "R =", R, "2-selfconj K:", sc, "(a,b) counts:", dict(st), flush=True)
        for e in ex[:3]: print("  fail", e)
