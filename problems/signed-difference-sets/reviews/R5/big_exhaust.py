"""Chunked A5 orbit exhaust (all leaves, FFT test) for one Instance key; prefix-split to bound memory.
Usage: big_exhaust.py <key> <prefixlen> <out>. Resumable: skips prefixes already logged."""
import sys, math, itertools, os; sys.path.insert(0, '.')
from common import *
from a5_check import suffix_tables
import numpy as np
key, j, outp = sys.argv[1], int(sys.argv[2]), sys.argv[3]
v, k, lam, sh = parse_key(key); n = k - lam; s2 = n + lam * v; s = math.isqrt(s2)
M = mult_group(n, math.lcm(*sh)); lab, r = orbits(sh, M); lab = np.array(lab)
sizes = np.bincount(lab, minlength=r).tolist(); suf = suffix_tables(sizes, k)
F = np.stack([np.fft.fftn((lab == i).reshape(sh).astype(float)).ravel() for i in range(r)])
done = set(l.split()[0] for l in open(outp)) if os.path.exists(outp) else set()
fo = open(outp, 'a'); total = 0
for pre in itertools.product((1, -1, 0), repeat=j):
    tag = ''.join('+-0'[(1, -1, 0).index(e)] for e in pre)
    if tag in done: continue
    c0 = sum(abs(e) * sizes[i] for i, e in enumerate(pre)); s0 = sum(e * sizes[i] for i, e in enumerate(pre))
    if not (0 <= k - c0 and abs(s - s0) <= k and suf[j][k - c0, s - s0 + k] > 0):
        fo.write(f"{tag} 0 none\n"); continue
    E = np.zeros((1, r), dtype=np.int8); E[0, :j] = pre; C = np.array([c0]); S = np.array([s0])
    for i in range(j, r):
        z = sizes[i]; parts = []
        for e in (1, -1, 0):
            c2 = C + abs(e) * z; s2_ = S + e * z; rc = k - c2; rs = s - s2_
            idx = np.nonzero((rc >= 0) & (np.abs(rs) <= k))[0]
            idx = idx[suf[i + 1][rc[idx], rs[idx] + k] > 0]
            E2 = E[idx].copy(); E2[:, i] = e; parts.append((E2, c2[idx], s2_[idx]))
        E = np.concatenate([p[0] for p in parts]); C = np.concatenate([p[1] for p in parts]); S = np.concatenate([p[2] for p in parts])
    res = 'none'
    for b in range(0, len(E), 50000):
        P = np.abs(E[b:b + 50000].astype(float) @ F) ** 2
        g = (np.abs(P[:, 1:] - n) < 0.5).all(axis=1) & (np.abs(P[:, 0] - s2) < 0.5)
        if g.any(): res = 'FOUND ' + str(E[b + int(np.nonzero(g)[0][0])].tolist()); break
    total += len(E); fo.write(f"{tag} {len(E)} {res}\n"); fo.flush()
    if res != 'none': break
print('r', r, 'sizes', sizes, 'leaves this run', total)
