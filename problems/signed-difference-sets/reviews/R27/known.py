"""Refuter A7, check 2: every object O* with gcd(v, n) = 1: verify it is an SDS, then on every quotient
H = Z_d1 x ... (d_i | m_i, |H| > 1, gcd(|H|, n) = 1, |H| <= 300) compute its coset sums, check one translate is
fixed by every t in M (t = p^f mod exp H for each p | n), and that search() finds a vector for each t in M."""
import glob, itertools, math, os, re, sys, time
import numpy as np
from search import search, elements
P = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
def isprime(p): return p > 1 and all(p % q for q in range(2, math.isqrt(p) + 1))
def mgroup(ds, n):
    e = math.lcm(*ds)
    if e == 1: return [1]
    sets = []
    for p in [p for p in range(2, n + 1) if n % p == 0 and isprime(p)]:
        sets.append({pow(p, f, e) for f in range(2 * e)})
    M = set.intersection(*sets) if sets else set(range(e))
    return sorted(x for x in M if math.gcd(x, e) == 1)
out = []
for f in sorted(glob.glob(os.path.join(P, 'objects', 'O*.txt')), key=lambda s: int(re.findall(r'O(\d+)', s)[0])):
    L = open(f).read().split('\n')
    m = re.match(r'(\S+) \((\d+),(\d+),(-?\d+)\)', L[0])
    ms = [int(x) for x in m.group(1).replace('C', '').split('x')]
    v, k, lam = int(m.group(2)), int(m.group(3)), int(m.group(4))
    n = k - lam
    name = os.path.basename(f)[:-4]
    if len(sys.argv) > 1 and name not in sys.argv[1:]: continue
    if n <= 0 or math.gcd(v, n) != 1: continue
    D = {}
    for l in L[1:]:
        if not l.strip(): continue
        *co, sg = l.split()
        D[tuple(int(x) for x in co)] = 1 if sg == '+' else -1
    E = elements(ms)
    a = np.array([D.get(e, 0) for e in E])
    # SDS check
    idx = {e: i for i, e in enumerate(E)}
    ok = len(D) == k and all(sum(a[idx[x]] * a[idx[tuple((xi + gi) % mi for xi, gi, mi in zip(x, g, ms))]] for x in E) == lam
                             for g in E[1:])
    for ds in itertools.product(*[[d for d in range(1, mi + 1) if mi % d == 0] for mi in ms]):
        ds = list(ds); H = math.prod(ds)
        if H == 1 or H > 300 or math.gcd(H, n) != 1: continue
        c = v // H
        EH = elements(ds); iH = {e: i for i, e in enumerate(EH)}
        cs = np.zeros(H, dtype=np.int64)
        for e in E: cs[iH[tuple(x % d for x, d in zip(e, ds))]] += a[idx[e]]
        M = [t for t in mgroup(ds, n) if t != 1] or [1]
        def shifted(b): return np.array([cs[iH[tuple((x + y) % d for x, y, d in zip(h, b, ds))]] for h in EH])
        fixed = any(all(all(sh[iH[tuple((t * x) % d for x, d in zip(h, ds))]] == sh[iH[h]] for h in EH) for t in M)
                    for sh in (shifted(b) for b in EH))
        s = int(cs.sum())
        res = []
        for t in M[:3]:
            r = search(ds, c, k, lam, t, abs(s), cap=300_000)
            res.append((t, r[0], r[1]))
        line = f'{name} {ms} ({v},{k},{lam}) n={n} H={ds} c={c} SDS={ok} fixed={fixed} ' + ' '.join(f't={t}:{r}:{l}' for t, r, l in res)
        print(line, flush=True); out.append(line)
