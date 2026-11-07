"""How many exists rows have a C5 quotient at all (so the C7 truth test is not vacuous)?"""
import csv, re, os, sys, math, itertools
PF = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
sys.path.insert(0, os.path.join(PF, 'solver'))
import selfconj as sc, markedcounts as mc
tot = 0; reach = 0; tested = 0
for row in csv.DictReader(open(os.path.join(PF, 'instances.csv'), encoding='utf-8')):
    if row['status'] != 'exists': continue
    mt = sc.KEY.fullmatch(row['key']); v, k, lam = map(int, mt.groups()[:3]); ms = [int(x) for x in mt[4].split(',')]
    tot += 1
    n = k - lam; S = k + lam * (v - 1)
    if n == 0 or S < 0 or math.isqrt(S) ** 2 != S: continue
    s = math.isqrt(S); found = False
    for p in sc.primes_of(n):
        if n % (p * p): continue
        for ds in itertools.product(*[sc.divisors(m) for m in ms]):
            h = math.prod(ds)
            if h == 1 or h % p == 0: continue
            if sc.conj_exp(p, math.lcm(*ds)) is None: continue
            found = True
            c = v // h; Q = k + lam * (c - 1); q = p
            npass = sum(1 for sp in (s, -s) for t in range(q) if sc.box_ok(h, q, sp, Q, t, c))
            tested += npass
    if found: reach += 1; print(row['id'], row['key'])
print('exists rows', tot, 'with a C5 quotient', reach, 'box-passing (s,t0) pairs tested at j=1', tested)
