# Positive control for indep.py's DFS (same constraints, copied): on every known SDS object and quotient with
# gcd(|H|, n) = 1, every t in M' \ {1} (up to 4): the true fixed translate (sum normalized to +|s|) must survive.
import os, re, itertools
from math import prod, gcd
base = os.path.dirname(os.path.abspath(__file__))
prob = os.path.normpath(os.path.join(base, '..', '..', '..'))
exec(open(os.path.join(base, 'objtest.py'), encoding='utf-8').read().split('stats = dict')[0])  # primes, val, divisors
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
    out, vals = [], [0] * len(cls)
    st = [0]
    def dfs(i, S, SQ, A, M):
        st[0] += 1
        if st[0] > 2_000_000: raise TimeoutError
        if i == len(cls):
            if S != s or SQ != Q or A > k or M < k or (s - k) % 2: return
            a = [0] * Hn
            for o, val in zip(cls, vals):
                for x in o: a[x] = val
            for gi in range(1, Hn):
                if sum(a[h] * a[adds[gi][h]] for h in range(Hn)) != lam * c: return
            out.append(tuple(a)); return
        R = suffix[i + 1]; z = sizes[i]
        for val in range(-c, c + 1):
            S2, SQ2 = S + z * val, SQ + z * val * val
            if SQ2 > Q: continue
            rs, rq = s - S2, Q - SQ2
            if abs(rs) > c * R or rq > c * c * R or rs * rs > R * rq: continue
            vals[i] = val; dfs(i + 1, S2, SQ2, A + z * abs(val), M + z * mm(val))
    dfs(0, 0, 0, 0, 0)
    return out, H, idx
tests = fails = capped = 0
for f in sorted(x for x in os.listdir(os.path.join(prob, 'objects')) if x.endswith('.txt')):
    lines = open(os.path.join(prob, 'objects', f), encoding='utf-8').read().split('\n')
    hdr = re.match(r'(\S+) \((\d+),(\d+),(-?\d+)\)', lines[0])
    ms = [int(x) for x in hdr.group(1).replace('C', '').split('x')]
    v, k, lam = int(hdr.group(2)), int(hdr.group(3)), int(hdr.group(4)); n = k - lam
    if n <= 0: continue
    D = {}
    for l in lines[1:]:
        tk = l.split()
        if tk: D[tuple(int(x) for x in tk[:-1])] = 1 if tk[-1] == '+' else -1
    for ds in itertools.product(*[divisors(m) for m in ms]):
        Hn = prod(ds)
        if Hn == 1 or gcd(Hn, n) != 1 or Hn > 120: continue
        c = v // Hn; e = 1
        for d in ds: e = e * d // gcd(e, d)
        a = {}
        for x, sg in D.items():
            h = tuple(xi % d for xi, d in zip(x, ds)); a[h] = a.get(h, 0) + sg
        def ok_t(t):
            if gcd(t, Hn) != 1: return False
            for p in primes(n):
                c10 = any(all(t % d == pow(p, ff, d) % d for d in ds) for ff in range(e + 1))
                sc = any(all((p ** i + 1) % d == 0 for d in ds) for i in range(1, e + 1)) and val(n, p) % 2 == 0
                if not (c10 or sc): return False
            return True
        Mp = [t for t in range(2, e) if ok_t(t)][:4]
        S = sum(a.values()); s = abs(S); sg = 1 if S >= 0 else -1
        for t in Mp:
            try: out, H, idx = search(list(ds), c, k, lam, t, s)
            except TimeoutError: print('capped', f, ds, t, flush=True); capped += 1; continue
            # true translates fixed by t, normalized
            want = []
            for b in H:
                ab = [sg * a.get(tuple((x + y) % d for x, y, d in zip(h, b, ds)), 0) for h in H]
                if all(ab[idx[tuple((t * x) % d for x, d in zip(h, ds))]] == ab[idx[h]] for h in H): want.append(tuple(ab))
            tests += 1
            if not want or not all(w in out for w in want):
                fails += 1; print('FAIL', f, ds, t, len(want), len(out))
print('tests', tests, 'fails', fails, 'capped', capped)
