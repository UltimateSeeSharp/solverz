# The C25 rule must fire on no `exists` row: for each exists row, each product quotient H (|H| <= 150) with
# gcd(|H|, n) = 1, the t in M' \ {1} with fewest classes; the DFS of indep.py (copied, node cap) must find >= 1
# vector with sum s = sqrt(k + lam (v-1)) (s = 0 too). 0 vectors on an exists row = the rule kills it = refutation.
import csv, os, re, itertools, sys, time
from math import prod, gcd, isqrt
base = os.path.dirname(os.path.abspath(__file__))
prob = os.path.normpath(os.path.join(base, '..', '..', '..'))
exec(open(os.path.join(base, 'objtest.py'), encoding='utf-8').read().split('stats = dict')[0])
CAP = 3_000_000
def search(ds, c, k, lam, t, s):
    Hn = prod(ds); n = k - lam
    H = list(itertools.product(*[range(d) for d in ds])); idx = {h: i for i, h in enumerate(H)}
    mul = lambda h: tuple((t * x) % d for x, d in zip(h, ds))
    seen, cls = set(), []
    for h in H:
        if h in seen: continue
        o, x = [], h
        while x not in seen: seen.add(x); o.append(idx[x]); x = mul(x)
        cls.append(o)
    cls.sort(key=len, reverse=True); sizes = [len(o) for o in cls]
    suffix = [sum(sizes[i:]) for i in range(len(sizes) + 1)]
    Q = n + lam * c; mm = lambda a: c if (c - a) % 2 == 0 else c - 1
    adds = [[idx[tuple((x + y) % d for x, y, d in zip(h, g, ds))] for h in H] for g in H]
    st = dict(found=0, nodes=0); vals = [0] * len(cls)
    class Done(Exception): pass
    def dfs(i, S, SQ, A, M):
        st['nodes'] += 1
        if st['nodes'] > CAP: raise Done
        if i == len(cls):
            if S != s or SQ != Q or A > k or M < k or (s - k) % 2: return
            a = [0] * Hn
            for o, val in zip(cls, vals):
                for x in o: a[x] = val
            for gi in range(1, Hn):
                if sum(a[h] * a[adds[gi][h]] for h in range(Hn)) != lam * c: return
            st['found'] += 1; raise Done
        R = suffix[i + 1]; z = sizes[i]
        for val in range(-c, c + 1):
            S2, SQ2 = S + z * val, SQ + z * val * val
            if SQ2 > Q: continue
            rs, rq = s - S2, Q - SQ2
            if abs(rs) > c * R or rq > c * c * R or rs * rs > R * rq: continue
            vals[i] = val; dfs(i + 1, S2, SQ2, A + z * abs(val), M + z * mm(val))
    try: dfs(0, 0, 0, 0, 0)
    except Done: pass
    return st['found'], st['nodes'] > CAP, len(cls)
res = dict(ok=0, capped=0, killed=0, noquot=0)
for r in csv.DictReader(open(os.path.join(prob, 'instances.csv'), encoding='utf-8')):
    if r['status'] != 'exists': continue
    m = re.match(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)', r['key'])
    v, k, lam = int(m.group(1)), int(m.group(2)), int(m.group(3)); ms = [int(x) for x in m.group(4).split(',')]
    n = k - lam; s2 = k + lam * (v - 1)
    if n <= 0 or s2 < 0 or isqrt(s2) ** 2 != s2: print('skip', r['id'], r['key']); continue
    s = isqrt(s2); any_q = False
    for ds in itertools.product(*[divisors(mm_) for mm_ in ms]):
        Hn = prod(ds)
        if Hn == 1 or Hn > 150 or gcd(Hn, n) != 1: continue
        e = 1
        for d in ds: e = e * d // gcd(e, d)
        def ok_t(t):
            if gcd(t, Hn) != 1: return False
            for p in primes(n):
                c10 = any(all(t % d == pow(p, ff, d) % d for d in ds) for ff in range(e + 1))
                sc = any(all((p ** i + 1) % d == 0 for d in ds) for i in range(1, e + 1)) and val(n, p) % 2 == 0
                if not (c10 or sc): return False
            return True
        Mp = [t for t in range(2, e) if ok_t(t)]
        if not Mp: continue
        def ncls(t):
            seen = set(); cnt = 0
            for h in itertools.product(*[range(d) for d in ds]):
                if h in seen: continue
                cnt += 1; x = h
                while x not in seen: seen.add(x); x = tuple((t * y) % d for y, d in zip(x, ds))
            return cnt
        t = min(Mp, key=ncls); any_q = True
        f, capped, nc = search(list(ds), v // Hn, k, lam, t, s)
        if f: res['ok'] += 1
        elif capped: res['capped'] += 1; print('capped', r['id'], r['key'], ds, t, nc)
        else: res['killed'] += 1; print('KILLS EXISTS ROW', r['id'], r['key'], ds, t, nc, flush=True)
    if not any_q: res['noquot'] += 1
print(res)
