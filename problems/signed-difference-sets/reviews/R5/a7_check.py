"""Independent recheck of A7 kills: on the killing quotient H (coordinatewise d_i | m_i), own M_H and orbits,
every orbit-constant a in [-c,c] with sum = +-s and sum of squares n + lam c (numpy reachability on
(sum, sumsq)), then support bookkeeping and FFT on H (|a^(chi)|^2 = n, chi != 1). Count survivors.
Usage: a7_check.py <out> [validate]"""
import sys, glob, ast, math; sys.path.insert(0, '.')
from common import *
import numpy as np
def a7_count(v, k, lam, ds, sign):
    n = k - lam; o = math.prod(ds); c = v // o; s = sign * math.isqrt(n + lam * v); Q = n + lam * c
    M = mult_group(n, math.lcm(*ds)); lab, r = orbits(ds, M); lab = np.array(lab)
    sz = np.bincount(lab, minlength=r).tolist(); B = v
    reach = [None] * (r + 1); t = np.zeros((2 * B + 1, Q + 1), dtype=bool); t[B, 0] = True; reach[r] = t
    for i in range(r - 1, -1, -1):
        z = sz[i]; u = np.zeros_like(t); prev = reach[i + 1]
        for x in range(-c, c + 1):
            ds_, dq = z * x, z * x * x
            if dq > Q: continue
            sh = np.zeros_like(prev)
            if ds_ >= 0: sh[ds_:, dq:] = prev[:2 * B + 1 - ds_, :Q + 1 - dq]
            else: sh[:ds_, dq:] = prev[-ds_:, :Q + 1 - dq]
            u |= sh
        reach[i] = u
    if not reach[0][s + B, Q]: return r, 0, 0
    X = np.zeros((1, r), dtype=np.int16); S = np.zeros(1, dtype=np.int64); SQ = np.zeros(1, dtype=np.int64)
    for i in range(r):
        z = sz[i]; parts = []
        for x in range(-c, c + 1):
            S2 = S + z * x; Q2 = SQ + z * x * x; rs = s - S2; rq = Q - Q2
            idx = np.nonzero((rq >= 0) & (np.abs(rs) <= B))[0]
            idx = idx[reach[i + 1][rs[idx] + B, rq[idx]]]
            X2 = X[idx].copy(); X2[:, i] = x; parts.append((X2, S2[idx], Q2[idx]))
        X = np.concatenate([p[0] for p in parts]); S = np.concatenate([p[1] for p in parts]); SQ = np.concatenate([p[2] for p in parts])
    nleaf = len(X); szv = np.array(sz)
    A = (np.abs(X) * szv).sum(axis=1)
    maxm = np.where((c - X) % 2 == 0, c, c - 1); MM = (maxm * szv).sum(axis=1)
    ok = (A <= k) & (MM >= k) & ((k - A) % 2 == 0)
    X = X[ok]
    if len(X) == 0: return r, nleaf, 0
    F = np.stack([np.fft.fftn((lab == i).reshape(ds).astype(float)).ravel() for i in range(r)])
    P = np.abs(X.astype(float) @ F) ** 2
    good = (np.abs(P[:, 1:] - n) < 0.5).all(axis=1)
    return r, nleaf, int(good.sum())
if __name__ == '__main__':
    out = open(sys.argv[1], 'w')
    if len(sys.argv) > 2:  # validation: quotients of known sets must give >= 1 vector
        sys.path.insert(0, RSC); import known_sets, constructions, itertools
        tot = bad = 0
        for src in (known_sets.gordon_sets(), known_sets.project_sets(), constructions.all_sets()):
            for name, shape, k, lam, Ar in src:
                Ar = np.asarray(Ar).reshape(list(shape)); v = Ar.size; n = k - lam
                if not known_sets.is_sds(Ar, k, lam) or v > 200: continue
                for ds in itertools.product(*[[x for x in range(1, m + 1) if m % x == 0] for m in shape]):
                    h = math.prod(ds)
                    if h == 1 or math.gcd(h, n) != 1 or len(mult_group(n, math.lcm(*ds))) == 1: continue
                    r = orbits(list(ds), mult_group(n, math.lcm(*ds)))[1]
                    if r > 10: continue
                    rr, nl, g = a7_count(v, k, lam, tuple(ds), 1); tot += 1
                    if g == 0: bad += 1; out.write(f"VALIDATION_FAIL {name} {ds}\n")
        out.write(f"# validation: {tot} quotients of known sets, {bad} with no vector\n"); sys.exit()
    for p in sorted(glob.glob(IDEA + '/mc_*.out') + glob.glob(IDEA + '/mcb_*.out')):
        for l in open(p):
            x = l.split(None, 2); res = ast.literal_eval(x[2].strip())
            if res[0] != 'KILL': continue
            v, k, lam, sh = parse_key(x[1]); ds = tuple(res[1])
            r1, l1, g1 = a7_count(v, k, lam, ds, 1); r2, l2, g2 = a7_count(v, k, lam, ds, -1)
            out.write(f"{x[0]} {x[1]} H={list(ds)} r={r1} theirs_r={res[2]} leaves+={l1} leaves-={l2} good={g1 + g2}\n"); out.flush()
