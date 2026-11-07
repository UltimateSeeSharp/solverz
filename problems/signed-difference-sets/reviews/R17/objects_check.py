"""On every object O1-O39: verify the SDS, then test the facts C17, C7 and C15 use on the actual set, and that no
certificate the generators would emit kills it."""
import os, re, sys, math, glob, itertools
PF = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(PF, 'solver'))
import selfconj as sc, markedcounts as mc, orbitrows as orb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from truth_check import rc_kills, even_quot

def load(f):
    lines = open(f, encoding='utf-8').read().split('\n')
    m = re.fullmatch(r'(\S+) \((\d+),(\d+),(-?\d+)\)', lines[0].strip())
    ms = [int(x) for x in m[1].replace('C', '').split('x')]
    D = {}
    for l in lines[1:]:
        if not l.strip(): continue
        *c, sg = l.split()
        D[tuple(int(x) % mm for x, mm in zip(c, ms))] = 1 if sg == '+' else -1
    return ms, int(m[2]), int(m[3]), int(m[4]), D

def add(x, g, ms): return tuple((a + b) % m for a, b, m in zip(x, g, ms))

for f in sorted(glob.glob(os.path.join(PF, 'objects', 'O*.txt')), key=lambda s: int(re.search(r'O(\d+)', s)[1])):
    name = os.path.basename(f)[:-4]
    ms, v, k, lam, D = load(f)
    assert math.prod(ms) == v and len(D) == k, (name, 'size')
    n, S = k - lam, k + lam * (v - 1)
    s_act = sum(D.values())
    assert s_act * s_act == S, (name, 'C1')
    elems = list(itertools.product(*[range(m) for m in ms]))
    if v <= 500:
        for g in elems[1:]:
            assert sum(d * D.get(add(x, g, ms), 0) for x, d in D.items()) == lam, (name, 'corr', g)
        sds = 'SDS ok'
    else:
        sds = 'SDS not rechecked (v>500)'
    notes = []
    # C17
    R = sum(1 for m in ms if m % 2 == 0)
    for r in range(1, R + 1):
        eq = even_quot(ms, r)
        idx = [i for i, d in enumerate(eq) if d == 2]
        vals = []
        for u in itertools.product((0, 1), repeat=r):
            vals.append(sum(d * (-1) ** sum(ui * (x[i] % 2) for ui, i in zip(u, idx)) for x, d in D.items()))
        a0 = sum(d for x, d in D.items() if all(x[i] % 2 == 0 for i in idx))
        assert all(c * c == n for c in vals[1:]), (name, 'C17 chi^2', r, vals)
        assert sum(vals) == 2 ** r * a0, (name, 'C17 sum')
        mm = math.isqrt(n) if n >= 0 and math.isqrt(n) ** 2 == n else None
        if mm is not None and rc_kills(ms, k, lam, r, math.isqrt(S), mm):
            print('!!! C17 KILLS OBJECT', name, r)
    if R: notes.append(f'C17 facts ok r<={R}')
    # C7 / C5 / C14 on every quotient
    nq = 0
    if n > 0:
        for p in sc.primes_of(n):
            J, rest = 0, n
            while rest % (p * p) == 0: rest //= p * p; J += 1
            for j in range(1, J + 1):
                q = p ** j
                for ds in itertools.product(*[sc.divisors(m) for m in ms]):
                    h = math.prod(ds)
                    if h == 1 or h % p == 0 or sc.conj_exp(p, math.lcm(*ds)) is None: continue
                    c = v // h; Q = k + lam * (c - 1)
                    a = {}
                    for x, d in D.items():
                        key = tuple(xi % di for xi, di in zip(x, ds)); a[key] = a.get(key, 0) + d
                    cnt = {}
                    for x in D:
                        key = tuple(xi % di for xi, di in zip(x, ds)); cnt[key] = cnt.get(key, 0) + 1
                    hs = list(itertools.product(*[range(di) for di in ds]))
                    av = [a.get(hh, 0) for hh in hs]
                    t0 = av[0] % q
                    assert all((x - t0) % q == 0 for x in av), (name, 'C5 congr', p, j, ds)
                    assert all(abs(x) <= c for x in av) and sum(x * x for x in av) == Q and sum(av) in (S and (math.isqrt(S), -math.isqrt(S)) or (0,)), (name, 'moments', ds)
                    sm = sum(abs(x) for x in av); sM = sum(mc.maxm(c, x) for x in av)
                    assert sm <= k <= sM, (name, 'C7 bounds', ds, sm, k, sM)
                    assert all(abs(a.get(hh, 0)) <= cnt.get(hh, 0) <= mc.maxm(c, a.get(hh, 0)) for hh in hs)
                    assert sc.box_ok(h, q, sum(av), Q, t0, c), (name, 'C14 box fails on a real set', ds)
                    w = mc.weight(h, q, sum(av), Q, t0, c, k)
                    if w is not None and mc.check_weight(*w, h, q, sum(av), Q, t0, c, k):
                        print('!!! C7 WEIGHT KILLS OBJECT', name, p, j, ds, w)
                    nq += 1
    if nq: notes.append(f'C5/C7/C14 facts ok on {nq} quotients')
    # C15
    if n > 1 and orb.squarefree(n) and math.gcd(n, v) == 1:
        t = orb.generator(ms, n)
        fixed = [a for a in elems if all(D.get(add(tuple(t * xi % m for xi, m in zip(x, ms)), a, ms), 0) == D.get(add(x, a, ms), 0) for x in elems)]
        notes.append(f'C15 t={t} fixed translates {len(fixed)}')
        if not fixed: print('!!! C15 FAILS ON OBJECT', name, t)
        else:
            a = fixed[0]; s2 = sum(D.get(add(x, a, ms), 0) for x in elems)
            notes.append(f'orbitExhaust {ms} {k} {lam} {t} {abs(s2)}')
    print(name, ms, (v, k, lam), sds, '; '.join(notes))
