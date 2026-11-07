"""Refuter A7, check 2b: every `exists` row of instances.csv with n > 0 (gcd(v, n) arbitrary): on every quotient
H (d_i | m_i, 1 < |H| <= 300, gcd(|H|, n) = 1) and every t != 1 in M (none when M = {1}), search() must not
kill (C10 + an SDS => a t-fixed vector). One line per (row, H, t); 'killed' there refutes the rule."""
import csv, itertools, math, os, re, sys, time
from search import search
P = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
def isprime(p): return p > 1 and all(p % q for q in range(2, math.isqrt(p) + 1))
def mgroup(ds, n):
    e = math.lcm(*ds)
    if e == 1: return [1]
    sets = [{pow(p, f, e) for f in range(2 * e)} for p in range(2, n + 1) if n % p == 0 and isprime(p)]
    M = set.intersection(*sets) if sets else set(range(e))
    return sorted(x for x in M if math.gcd(x, e) == 1)
for r in csv.DictReader(open(os.path.join(P, 'instances.csv'), encoding='utf-8')):
    if r['status'] != 'exists': continue
    v, k, lam, fac = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]*)\]\)', r['key']).groups()
    v, k, lam = int(v), int(k), int(lam); ms = [int(x) for x in fac.split(',')]
    n = k - lam
    if n <= 0: continue
    s = math.isqrt(k + lam * (v - 1))
    assert s * s == k + lam * (v - 1)
    for ds in itertools.product(*[[d for d in range(1, mi + 1) if mi % d == 0] for mi in ms]):
        ds = list(ds); H = math.prod(ds)
        if H == 1 or H > 300 or math.gcd(H, n) != 1: continue
        c = v // H
        M = [t for t in mgroup(ds, n) if t != 1]
        for t in M[:3]:
            t0 = time.time()
            res, leaves, _ = search(ds, c, k, lam, t, s, cap=300_000)
            print(r['id'], ms, (v, k, lam), 'H', ds, 'c', c, 't', t, res, leaves, f'{time.time() - t0:.1f}', flush=True)
