"""Verify each object is an SDS, then apply the Lean-form rule with its actual sign sum."""
import re, glob, math
import numpy as np
from rows6 import lean_rule, vp
fires = 0
for f in sorted(glob.glob('../../../objects/O*.txt'), key=lambda s: int(re.findall(r'O(\d+)', s)[0])):
    lines = open(f, encoding='utf-8').read().strip().splitlines()
    m = re.match(r'(\S+) \((\d+),\s*(\d+),\s*(-?\d+)\)', lines[0])
    ms = [int(x) for x in re.findall(r'C(\d+)', m[1])]; v, k, lam = int(m[2]), int(m[3]), int(m[4])
    assert math.prod(ms) == v
    D = np.zeros(ms, dtype=np.int64)
    for l in lines[1:]:
        *c, sg = l.split(); D[tuple(int(x) for x in c)] = 1 if sg == '+' else -1
    assert np.count_nonzero(D) == k
    F = np.fft.fftn(D.astype(float)); ac = np.rint(np.fft.ifftn(F * np.conj(F)).real).astype(np.int64)
    ok = ac.flat[0] == k and all(x == lam for x in ac.flat[1:])
    s = int(D.sum())
    h = lean_rule(v, k, lam, ms)
    if h: fires += 1
    print(f.split('/')[-1], ms, (v, k, lam), 'SDS' if ok else 'NOT SDS', 's', s, 'FIRES' if h else '', h[:1])
print('fires', fires)
