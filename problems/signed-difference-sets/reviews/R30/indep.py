# Independent recheck of the 26 kills (no a7selfconj/a7rows code): for each row, enumerate integer coset-sum
# vectors a on H = prod Z_d constant on the orbits of x -> t x, |a| <= c, sum a = s, sum a^2 = n + lam c,
# sum |a| <= k <= sum maxMarked(a), sum a = k mod 2, autocorrelation lam*c at every g != 0.
# Optional C5 filter (all a(h) congruent mod q). Prints the number of survivors (expected 0).
import os, re, sys, itertools, time
from math import prod, gcd
base = os.path.dirname(os.path.abspath(__file__))
prob = os.path.normpath(os.path.join(base, '..', '..', '..'))
pat = re.compile(r'theorem n(\d+)_not_hasSDS : ¬ HasSDS \([^)]*\) (\d+) (\d+) :=\s*\n\s*not_hasSDS_of_cosetRow(\w+) '
                 r'\(ms := \[([\d, ]+)\]\) \(ds := \[([\d, ]+)\]\) \(c := (\d+)\) \(t := (\d+)\) \(s := (-?\d+)\)(?: \(q := (\d+)\))?')
rows = []
for p in (95, 96, 97, 98):
    txt = open(os.path.join(prob, 'lean/SignedDifferenceSets/CosetRows/Part%d.lean' % p), encoding='utf-8').read()
    for m in pat.finditer(txt):
        rows.append(dict(id='N' + m.group(1), k=int(m.group(2)), lam=int(m.group(3)), kind=m.group(4),
                         ms=[int(x) for x in m.group(5).split(',')], ds=[int(x) for x in m.group(6).split(',')],
                         c=int(m.group(7)), t=int(m.group(8)), s=int(m.group(9)),
                         q=int(m.group(10)) if m.group(10) else None))
assert len(rows) == 26, len(rows)
only = sys.argv[1:] 
use_filter = os.environ.get('FILTER', '0') == '1'
for r in rows:
    if only and r['id'] not in only: continue
    k, lam, ds, c, t, s = r['k'], r['lam'], r['ds'], r['c'], r['t'], r['s']
    v = prod(r['ms']); n = k - lam; Hn = prod(ds)
    assert v == c * Hn and s * s == k + lam * (v - 1) and gcd(Hn, n) == 1 and gcd(t, Hn) == 1
    H = list(itertools.product(*[range(d) for d in ds]))
    idx = {h: i for i, h in enumerate(H)}
    mul = lambda h: tuple((t * x) % d for x, d in zip(h, ds))
    seen, cls = set(), []
    for h in H:
        if h in seen: continue
        o, x = [], h
        while x not in seen: seen.add(x); o.append(idx[x]); x = mul(x)
        cls.append(o)
    cls.sort(key=len, reverse=True)
    sizes = [len(o) for o in cls]
    suffix = [sum(sizes[i:]) for i in range(len(sizes) + 1)]
    Q = n + lam * c
    mm = lambda a: c if (c - a) % 2 == 0 else c - 1
    adds = [[idx[tuple((x + y) % d for x, y, d in zip(h, g, ds))] for h in H] for g in H]
    q = r['q'] if (use_filter and r['q']) else None
    found, leaves = 0, 0
    vals = [0] * len(cls)
    t0 = time.time()
    def dfs(i, S, SQ, A, M):
        global found, leaves
        if i == len(cls):
            leaves += 1
            if S != s or SQ != Q or A > k or M < k or (s - k) % 2: return
            a = [0] * Hn
            for o, val in zip(cls, vals):
                for x in o: a[x] = val
            for gi in range(1, Hn):
                ad = adds[gi]
                if sum(a[h] * a[ad[h]] for h in range(Hn)) != lam * c: return
            found += 1
            print('  SURVIVOR', r['id'], vals)
            return
        R = suffix[i + 1]; z = sizes[i]
        for val in range(-c, c + 1):
            if q and i > 0 and (val - vals[0]) % q: continue
            S2, SQ2 = S + z * val, SQ + z * val * val
            if SQ2 > Q: continue
            rs, rq = s - S2, Q - SQ2
            if abs(rs) > c * R or rq > c * c * R or rs * rs > R * rq: continue
            if R == 0 and (rs or rq): continue
            vals[i] = val
            dfs(i + 1, S2, SQ2, A + z * abs(val), M + z * mm(val))
    dfs(0, 0, 0, 0, 0)
    print(r['id'], r['kind'], 'H', ds, 'c', c, 't', t, 'classes', len(cls), 'filter q', q, 'leaves', leaves,
          'survivors', found, '%.1fs' % (time.time() - t0), flush=True)
