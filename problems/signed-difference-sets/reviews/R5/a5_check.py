"""Independent recheck of every A5 kill ('none' in ideator oe_*.out): own multiplier group and orbits,
knapsack solution count by numpy DP (compare with their leaf count), then every knapsack solution
(sum +s; -s are negations) tested by FFT on G: |D^(chi)|^2 = n for chi != 1. Resumable.
Usage: a5_check.py <out> i/N"""
import sys, glob, math; sys.path.insert(0, '.')
from common import *
import numpy as np
def suffix_tables(sizes, k):
    r = len(sizes); W = 2 * k + 1
    suf = [None] * (r + 1); t = np.zeros((k + 1, W), dtype=np.int64); t[0, k] = 1; suf[r] = t
    for i in range(r - 1, -1, -1):
        z = sizes[i]; u = suf[i + 1].copy(); prev = suf[i + 1]
        if z <= k:
            u[z:, z:] += prev[:k + 1 - z, :W - z]      # +1: count +z, sum +z
            u[z:, :W - z] += prev[:k + 1 - z, z:]      # -1: count +z, sum -z
        suf[i] = u
    return suf
def leaves(sizes, k, s, suf):
    r = len(sizes); E = np.zeros((1, r), dtype=np.int8); C = np.zeros(1, dtype=np.int64); S = np.zeros(1, dtype=np.int64)
    for i in range(r):
        z = sizes[i]; parts = []
        for e in (1, -1, 0):
            c2 = C + abs(e) * z; s2 = S + e * z
            rc = k - c2; rs = s - s2
            ok = (rc >= 0) & (np.abs(rs) <= k)
            idx = np.nonzero(ok)[0]
            ok2 = suf[i + 1][rc[idx], rs[idx] + k] > 0
            idx = idx[ok2]
            E2 = E[idx].copy(); E2[:, i] = e; parts.append((E2, c2[idx], s2[idx]))
        E = np.concatenate([p[0] for p in parts]); C = np.concatenate([p[1] for p in parts]); S = np.concatenate([p[2] for p in parts])
    return E
def check(v, k, lam, shape):
    n = k - lam; s2 = n + lam * v; s = math.isqrt(s2)
    if s * s != s2: return 'nonsquare', 0, 0, 0
    e = math.lcm(*shape); M = mult_group(n, e); lab, r = orbits(shape, M)
    lab = np.array(lab); sizes = np.bincount(lab, minlength=r).tolist()
    suf = suffix_tables(sizes, k)
    cnt_p = int(suf[0][k, s + k]); cnt_m = int(suf[0][k, -s + k])
    if cnt_p == 0: return 'none', r, cnt_p, cnt_m
    F = np.stack([np.fft.fftn((lab == i).reshape(shape).astype(float)).ravel() for i in range(r)])
    E = leaves(sizes, k, s, suf); assert len(E) == cnt_p
    for b in range(0, len(E), 20000):
        X = E[b:b + 20000].astype(float) @ F; P = np.abs(X) ** 2
        good = (np.abs(P[:, 1:] - n) < 0.5).all(axis=1) & (np.abs(P[:, 0] - s2) < 0.5)
        if good.any(): return 'SDS_FOUND ' + str(E[b + int(np.nonzero(good)[0][0])].tolist()), r, cnt_p, cnt_m
    return 'none', r, cnt_p, cnt_m
if __name__ == '__main__':
    out = sys.argv[1]; ci, cn = map(int, sys.argv[2].split('/'))
    done = set()
    for p in glob.glob('a5chk_*.out'):
        done |= {l.split()[0] for l in open(p)}
    rows = [l.split() for p in sorted(glob.glob(IDEA + '/oe_*.out')) for l in open(p)]
    todo = [x for x in rows if x[3] == 'none' and x[0] not in done][ci::cn]
    with open(out, 'a') as fo:
        for x in todo:
            v, k, lam, sh = parse_key(x[1])
            res, r, cp, cm = check(v, k, lam, sh)
            fo.write(f"{x[0]} {x[1]} theirs_r={x[2]} theirs_cnt={x[4]} mine_r={r} cnt+={cp} cnt-={cm} {res}\n"); fo.flush()
