"""The lemma against E8's data: on every quotient where E8 found a contraction vector, and every
qualifying p (|V|^h <= 10^6), enumerate V^h for vectors with sum s, sum of squares n + lam c and
autocorrelation lam c at every shift != 0. E8 found one, the lemma puts it (up to sign) in V^h,
so the enumeration must find >= 1. For A2 triples, also record whether some vector meets
sum|a| <= k <= sum maxm and parity. Usage: python e8_lemma.py <out> <worker> <nworkers>"""
import sys, math, itertools, ctypes, os
ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from xcommon import primefac, self_conj, s_of, SCR, KEY
from xrules import V_of, maxm
out, w, nw = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
jobs = {}
for l in open(SCR + '/e8/combined.out', encoding='utf-8'):
    t = l.split()
    if len(t) < 4 or t[3] != 'open': continue
    mm = KEY.fullmatch(t[1]); v, k, lam = int(mm[1]), int(mm[2]), int(mm[3]); n = k - lam; s = s_of(v, k, lam)
    for item in t[4:]:
        H, flag = item.rsplit(':', 1)
        if flag != 'found': continue
        fs = tuple(int(x) for x in H.strip('[]').split(',')); h, m = math.prod(fs), math.lcm(*fs); c = v // h
        for p, e in primefac(n).items():
            if e < 2 or h % p == 0 or not self_conj(p, m): continue
            V = tuple(V_of(c, h, s, p ** (e // 2)))
            if len(V) ** h > 10 ** 6: continue
            key = (fs, V, s, n + lam * c, lam * c, k, c)
            jobs.setdefault(key, []).append(t[0])
jobs = sorted(jobs.items())
def shifts(fs):
    els = list(itertools.product(*[range(f) for f in fs])); idx = {e: i for i, e in enumerate(els)}
    return np.array([[idx[tuple((a + b) % f for a, b, f in zip(x, g, fs))] for x in els] for g in els])
with open(out, 'w') as fo:
    for ji, ((fs, V, s, Q, mu, k, c), ids) in enumerate(jobs):
        if ji % nw != w: continue
        h = math.prod(fs); add = shifts(fs)
        Va = np.array(V, dtype=np.int64)
        I = np.array(list(itertools.product(range(len(V)), repeat=h)), dtype=np.int64)
        A = Va[I]
        A = A[(A.sum(1) == s) & ((A * A).sum(1) == Q)]
        ok = np.ones(len(A), dtype=bool)
        for g in range(1, h):
            ok &= (A * A[:, add[g]]).sum(1) == mu
        A = A[ok]
        a2 = 0
        for a in A:
            Aab = int(np.abs(a).sum()); M = sum(maxm(int(x), c) for x in a)
            a2 += (Aab <= k <= M and (k - Aab) % 2 == 0)
        fo.write(f"{','.join(ids)} H={list(fs)} |V|={len(V)} vectors={len(A)} meeting_A2={a2}\n"); fo.flush()
