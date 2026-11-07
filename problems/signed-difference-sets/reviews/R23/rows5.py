"""Round 5 refuter: independent recompute of C21's open kills and comparison with MaRows parts.
Own code; reads instances.csv, the MaRows Lean sources, settle-c21.tsv, objects/_objects.md."""
import csv, re, sys, os, json
from math import gcd
ROOT = sys.argv[1]
LEAN = os.path.join(ROOT, 'lean/SignedDifferenceSets/MaRows')

def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def vp(n, p):
    e = 0
    while n % p == 0: n //= p; e += 1
    return e

def selfconj_i(p, m):
    """smallest i >= 1 with p^i = -1 mod m, or None."""
    if m == 1: return 1
    if gcd(p, m) != 1: return None
    x = 1
    for i in range(1, 2 * m + 2):
        x = x * p % m
        if x == (m - 1) % m: return i
        if x == 1: return None
    return None

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def best(v, k, lam, ms):
    n = k - lam
    if n == 0: return None
    n = abs(n)
    out = None
    for p in factor(n):
        e = vp(n, p); b = e // 2
        if b < 1: continue
        j = max(vp(m, p) for m in ms)
        if j < 1: continue
        pp = [m // p ** vp(m, p) for m in ms]
        expK = 1
        for a in pp: expK = expK * a // gcd(expK, a)
        bestK = 1
        for m in divisors(expK):
            if selfconj_i(p, m) is None: continue
            size = 1
            for a in pp: size *= gcd(a, m)
            bestK = max(bestK, size)
        H = p ** j * bestK
        c = v // H
        assert v % H == 0
        if 2 * c < p ** b:
            out = (p, j, bestK, e, b, c)
            break
    return out

rows = list(csv.DictReader(open(os.path.join(ROOT, 'instances.csv'), newline='')))
byid = {}
mine = set(); allhit = {}
for r in rows:
    m = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]*)\]\)', r['key'])
    v, k, lam = int(m[1]), int(m[2]), int(m[3])
    ms = [int(x) for x in m[4].split(',')] if m[4] else []
    prod = 1
    for x in ms: prod *= x
    assert prod == v, r['key']
    byid[int(r['id'][1:])] = (v, k, lam, ms, r['status'], r['lean'], r['evidence'])
    h = best(v, k, lam, ms)
    if h:
        allhit[int(r['id'][1:])] = (r['status'], h)
        if r['status'] == 'open': mine.add(int(r['id'][1:]))

# parse parts
part = {}
for nn in range(1, 7):
    src = open(os.path.join(LEAN, f'Part{nn:02d}.lean'), encoding='utf-8').read()
    body = src.split(':= [', 1)[1].split(')]\n', 1)[0] + ')'
    body = re.sub(r'\s+', ' ', body)
    for mm in re.finditer(r'\(⟨(\d+), \[([\d, ]*)\], (\d+), (-?\d+)⟩, ⟨(\d+), (\d+), (\d+), (\d+), (\d+), \[([\d, ]*)\], (\[.*?\]\]), (\[.*?\]\])⟩\)', body):
        rid = int(mm[1]); ms = [int(x) for x in mm[2].split(',')] if mm[2].strip() else []
        k, lam = int(mm[3]), int(mm[4])
        cert = dict(p=int(mm[5]), r=int(mm[6]), i=int(mm[7]), e=int(mm[8]), b=int(mm[9]),
                    ks=[int(x) for x in mm[10].split(',')], A=json.loads(mm[11]), P=json.loads(mm[12]))
        assert rid not in part, rid
        part[rid] = (nn, ms, k, lam, cert)
    cnt = len(re.findall(r'\(⟨\d+, \[', body))
    print(f'Part{nn:02d}: parsed {sum(1 for x in part.values() if x[0]==nn)} entries, raw tuples {cnt}')
print('parts total', len(part))

# check each part row against instances.csv
bad = 0
statuses = {}
for rid, (nn, ms, k, lam, cert) in part.items():
    v, k2, lam2, ms2, st, lean, ev = byid[rid]
    statuses[st] = statuses.get(st, 0) + 1
    if (ms, k, lam) != (ms2, k2, lam2):
        bad += 1; print('MISMATCH', rid, ms, k, lam, 'csv', ms2, k2, lam2)
print('row/key mismatches', bad, 'statuses of part rows', statuses)

# my independent cert check (Kills semantics re-implemented)
def isprime(p): return p >= 2 and all(p % d for d in range(2, int(p ** .5) + 1))
def kills(ms, k, lam, c):
    p, r, i, e, b, ks, A, P = c['p'], c['r'], c['i'], c['e'], c['b'], c['ks'], c['A'], c['P']
    ds = [r * p] + ks
    ok = isprime(p) and r > 0 and i > 0 and all(m > 0 for m in ms) and ks != []
    ok &= all((p ** i + 1) % d == 0 for d in ks)
    ok &= len(A) == len(ds) and len(P) == len(ds)
    if not ok: return 'basic'
    # maps well defined: d | a_s * m_s
    for t, d in enumerate(ds):
        a = A[t] + [0] * len(ms)
        if any((a[s] * ms[s]) % d for s in range(len(ms))): return 'mapok'
    for t, d in enumerate(ds):
        x = P[t] + [0] * len(ms)
        img = [sum((A[u] + [0] * len(ms))[s] * x[s] for s in range(len(ms))) % ds[u] for u in range(len(ds))]
        if img != [1 % ds[u] if u == t else 0 for u in range(len(ds))]: return 'surj'
    prodms = 1
    for m in ms: prodms *= m
    H = r * p
    for d in ks: H *= d
    if prodms % H: return 'prod'
    n = k - lam
    if n == 0 or n % p ** e: return 'n'
    if not 2 * b <= e: return 'be'
    if not 2 * (prodms // H) < p ** b: return 'c'
    # r a power of p
    rr = r
    while rr % p == 0: rr //= p
    if rr != 1: return 'r-not-p-power'
    return 'ok'
res = {}
for rid, (nn, ms, k, lam, cert) in part.items():
    res.setdefault(kills(ms, k, lam, cert), []).append(rid)
print('my Kills check:', {k: len(v) for k, v in res.items()})
for k_, v_ in res.items():
    if k_ != 'ok': print(k_, v_[:20])

# compare sets
P = set(part)
print('my open hits', len(mine), '| parts', len(P), '| parts - mine', sorted(P - mine)[:20], '| mine - parts', len(mine - P))
extra = sorted(mine - P)
print('mine - parts (first 40):', extra[:40])
for rid in extra[:10]: print('  ', rid, byid[rid][:4], allhit[rid])
st_all = {}
for rid, (st, h) in allhit.items(): st_all[st] = st_all.get(st, 0) + 1
print('all hits by status', st_all)
print('exists rows hit:', [ (rid, byid[rid][:4]) for rid,(st,h) in allhit.items() if st=='exists'])

# settle tsv
tsv = [l.rstrip('\n').split('\t') for l in open(os.path.join(ROOT, 'scratch/settle-c21.tsv'), encoding='utf-8')]
ids = [int(x[0][1:]) for x in tsv]
print('tsv rows', len(tsv), 'unique', len(set(ids)), 'set == parts:', set(ids) == P)
badt = 0
for x in tsv:
    rid = int(x[0][1:]); nn = part[rid][0] if rid in part else None
    exp = [f'N{rid}', 'none', f'C21; MaRows part{nn:02d}', f'SignedDifferenceSets.MaRows.not_hasSDS_of_mem_part{nn:02d}'] if nn else None
    if x != exp: badt += 1; print('TSV', x, exp)
print('tsv mismatches', badt)

# objects
objs = open(os.path.join(ROOT, 'objects/_objects.md'), encoding='utf-8').read()
objids = set(int(x) for x in re.findall(r'\|\s*N(\d+)\s*\|', objs))
print('object instance ids', len(objids), 'in parts:', sorted(objids & P))
