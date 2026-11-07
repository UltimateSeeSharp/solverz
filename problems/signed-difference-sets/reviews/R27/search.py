"""Refuter A7: own exhaustive search for t-invariant coset-sum vectors on H = Z_d1 x ... x Z_dr.
Exact (sum, sum of squares) reachability by bitsets, then DFS over exactly the vectors with
sum = s and sum of squares = Q = k + lam (c - 1); each is tested for |a| <= c, sum|a| <= k, parity,
k <= sum maxMarked, and correlation lam*c at one shift per t-orbit. Independent of a7rows.py."""
import math, sys, time
import numpy as np
sys.setrecursionlimit(100000)

def elements(ds):
    out = [()]
    for d in ds:
        out = [e + (x,) for e in out for x in range(d)]
    return out

def setup(ds, t):
    E = elements(ds)
    idx = {e: i for i, e in enumerate(E)}
    N = len(E)
    mul = [idx[tuple((t * x) % d for x, d in zip(e, ds))] for e in E]
    orb = [-1] * N
    orbits = []
    for i in range(N):
        if orb[i] < 0:
            o, j = [], i
            while orb[j] < 0:
                orb[j] = len(orbits); o.append(j); j = mul[j]
            assert j == i, 'not a permutation'
            orbits.append(o)
    add = np.array([[idx[tuple((x + y) % d for x, y, d in zip(e, g, ds))] for e in E] for g in E])
    return E, np.array(orb), orbits, add

def search(ds, c, k, lam, t, s, cap=5_000_000, want_all=False):
    E, orb, orbits, add = setup(ds, t)
    Q = k + lam * (c - 1)
    z = [len(o) for o in orbits]
    m = len(z)
    mask = (1 << (Q + 1)) - 1 if Q >= 0 else 0
    R = [None] * (m + 1)
    R[m] = {0: 1}
    for i in range(m - 1, -1, -1):
        zi, cur = z[i], {}
        for sig, bits in R[i + 1].items():
            for x in range(-c, c + 1):
                b = (bits << (zi * x * x)) & mask
                if b:
                    key = sig + zi * x
                    cur[key] = cur.get(key, 0) | b
        R[i] = cur
    if Q < 0 or not ((R[0].get(s, 0) >> Q) & 1):
        return 'killed', 0, None
    shifts = [o[0] for o in orbits if o[0] != 0]     # one shift per nonzero t-orbit
    target = lam * c
    vals = [0] * m
    leaves = [0]
    found = []
    def leaf():
        a = np.array(vals, dtype=np.int64)[orb]
        ab = int(np.abs(a).sum())
        if ab > k or (k - ab) % 2: return False
        mm = int(np.where((c - a) % 2 == 0, c, c - 1).sum())
        if k > mm: return False
        if np.abs(a).max() > c: return False
        for g in shifts:
            if int(np.dot(a, a[add[g]])) != target: return False
        return True
    def dfs(i, sig, q):
        if leaves[0] > cap: return True
        if i == m:
            leaves[0] += 1
            if leaf():
                found.append(list(vals))
                return not want_all
            return False
        zi, nxt = z[i], R[i + 1]
        for x in range(-c, c + 1):
            q2 = q - zi * x * x
            if q2 < 0: continue
            s2 = sig - zi * x
            if (nxt.get(s2, 0) >> q2) & 1:
                vals[i] = x
                if dfs(i + 1, s2, q2): return True
        return False
    dfs(0, s, Q)
    if found: return 'found', leaves[0], found
    if leaves[0] > cap: return 'cap', leaves[0], None
    return 'killed', leaves[0], None
