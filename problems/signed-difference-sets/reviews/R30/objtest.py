# Independent numeric test of C25 (Lean form) on every known SDS in objects/: for each product quotient
# Grp ds (d_i | m_i) with gcd(|H|, n) = 1, some translate of the coset sums is fixed by every t of M'.
import os, re, itertools
from math import gcd, prod
base = os.path.dirname(os.path.abspath(__file__))
prob = os.path.normpath(os.path.join(base, '..', '..', '..'))
def primes(n):
    ps, p = [], 2
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: ps.append(n)
    return ps
def val(n, p):
    e = 0
    while n % p == 0: n //= p; e += 1
    return e
def divisors(m): return [d for d in range(1, m + 1) if m % d == 0]
stats = dict(objs=0, quots=0, bigger=0, fail=0, s2used=0)
for f in sorted(x for x in os.listdir(os.path.join(prob, 'objects')) if x.endswith('.txt')):
    lines = open(os.path.join(prob, 'objects', f), encoding='utf-8').read().split('\n')
    hdr = re.match(r'(\S+) \((\d+),(\d+),(-?\d+)\)', lines[0])
    ms = [int(x) for x in hdr.group(1).replace('C', '').split('x')]
    v, k, lam = int(hdr.group(2)), int(hdr.group(3)), int(hdr.group(4))
    D = {}
    for l in lines[1:]:
        t = l.split()
        if not t: continue
        D[tuple(int(x) for x in t[:-1])] = 1 if t[-1] == '+' else -1
    assert prod(ms) == v and len(D) == k
    # verify SDS
    elems = list(itertools.product(*[range(m) for m in ms]))
    add = lambda x, g: tuple((a + b) % m for a, b, m in zip(x, g, ms))
    for g in elems[1:min(len(elems), 40)]:
        assert sum(s * D.get(add(x, g), 0) for x, s in D.items()) == lam, f
    stats['objs'] += 1
    n = k - lam
    if n <= 0: continue
    for ds in itertools.product(*[divisors(m) for m in ms]):
        H = prod(ds)
        if H == 1 or gcd(H, n) != 1: continue
        stats['quots'] += 1
        a = {}
        for x, s in D.items():
            h = tuple(xi % d for xi, d in zip(x, ds)); a[h] = a.get(h, 0) + s
        Hel = list(itertools.product(*[range(d) for d in ds]))
        e = 1
        for d in ds: e = e * d // gcd(e, d)
        def ok_t(t, s2):
            if gcd(t, H) != 1: return False
            for p in primes(n):
                c10 = any(all(t % d == pow(p, f, d) % d for d in ds) for f in range(e + 1))
                sc = s2 and any(all((p ** i + 1) % d == 0 for d in ds) for i in range(1, e + 1)) and val(n, p) % 2 == 0
                if not (c10 or sc): return False
            return True
        Mp = [t for t in range(1, e + 1) if ok_t(t, True)]
        M10 = [t for t in range(1, e + 1) if ok_t(t, False)]
        if len(Mp) > len(M10): stats['bigger'] += 1
        mul = lambda t, h: tuple((t * hi) % d for hi, d in zip(h, ds))
        hadd = lambda h, b: tuple((x + y) % d for x, y, d in zip(h, b, ds))
        good = any(all(a.get(hadd(mul(t, h), b), 0) == a.get(hadd(h, b), 0) for t in Mp for h in Hel) for b in Hel)
        if not good:
            stats['fail'] += 1; print('FAIL', f, ms, k, lam, ds, Mp)
        elif len(Mp) > len(M10): stats['s2used'] += 1
print(stats)
