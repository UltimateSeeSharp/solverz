"""Independent check of Part33..Part59 rows against instances.csv, e10/e11, objects, settle-i13.tsv."""
import csv, re, sys, os, math
from math import gcd
P = sys.argv[1]  # problem folder
def parse_key(key):
    m = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)', key)
    v, k, l = int(m[1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(',')]
    assert math.prod(ms) == v, key
    return v, k, l, ms
def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def squarefree(n): return all(e == 1 for e in factor(n).values())
inst = {r['id']: r for r in csv.DictReader(open(os.path.join(P, 'instances.csv'), encoding='utf-8'))}
res = {}
for fn in ('scratch/e10.out', 'scratch/e11.out'):
    for line in open(os.path.join(P, fn)):
        a = line.split()
        if not a: continue
        assert a[0] not in res, ('dup', a[0]); res[a[0]] = (a[2], a[1], fn)
        assert inst[a[0]]['key'] == a[1], ('key mismatch', a)
objs = set()
for line in open(os.path.join(P, 'objects/_objects.md'), encoding='utf-8'):
    c = line.split('|')
    if len(c) > 5 and re.fullmatch(r'\s*O\d+\s*', c[1]):
        for nid in re.findall(r'N\d+', c[4]): objs.add(nid)
print('objects with instance ids:', len(objs))
# target
target = {}
for i, r in inst.items():
    v, k, l, ms = parse_key(r['key']); n = k - l
    if r['status'] != 'open' or i not in res or res[i][0] != 'none': continue
    if n <= 0 or gcd(v, n) != 1 or squarefree(n): continue
    target[i] = (v, k, l, ms)
print('target (open, E10/E11 none, n not squarefree, gcd(v,n)=1):', len(target))
# parts
thm = re.compile(r'theorem (n(\d+))_not_hasSDS : ¬ HasSDS \(([^)]*)\) (\d+) (\(?-?\d+\)?) :=\s*\n\s*not_hasSDS_of_orbitRow\' \(ms := \[([\d, ]+)\]\) \(t := (\d+)\) \(s := (-?\d+)\)\s*\n\s*\(by decide \+kernel\) _')
rows = {}; where = {}; errs = []
for part in range(33, 60):
    fn = os.path.join(P, f'lean/SignedDifferenceSets/OrbitRows/Part{part}.lean')
    txt = open(fn, encoding='utf-8').read()
    nthm = txt.count('theorem ')
    found = thm.findall(txt)
    if len(found) != nthm: errs.append(('unparsed theorems', part, nthm, len(found)))
    if 'sorry' in txt or 'native_decide' in txt or 'axiom' in txt: errs.append(('forbidden word', part))
    for name, num, grp, k, l, ms, t, s in found:
        i = 'N' + num
        gms = [int(x) for x in re.findall(r'ZMod (\d+)', grp)]
        if ' × '.join(f'ZMod {m}' for m in gms) != grp: errs.append(('group form', i, grp))
        ms = [int(x) for x in ms.split(',')]
        k, l, t, s = int(k), int(l.strip('()')), int(t), int(s)
        assert i not in rows, ('dup row', i)
        rows[i] = (gms, ms, k, l, t, s); where[i] = part
print('part rows:', len(rows))
for i, (gms, ms, k, l, t, s) in rows.items():
    r = inst.get(i)
    if r is None: errs.append(('no instance', i)); continue
    v0, k0, l0, ms0 = parse_key(r['key'])
    if gms != ms or ms != ms0 or k != k0 or l != l0: errs.append(('param mismatch', i, r['key'], gms, ms, k, l))
    if r['status'] != 'open': errs.append(('status', i, r['status']))
    if i in objs: errs.append(('has object', i))
    if res.get(i, ('?',))[0] != 'none': errs.append(('e10/e11', i, res.get(i)))
    if i not in target: errs.append(('not in target', i))
    v = math.prod(ms); n = k - l
    # OrbitRow' conditions except orbitExhaust
    if not (n > 0 and gcd(v, n) == 1 and gcd(t, v) == 1): errs.append(('coprime', i))
    if squarefree(n): errs.append(('n squarefree', i, n))
    for p in factor(n):
        if not any(all(t % m == pow(p, f, m) % m for m in ms) for f in range(v)):
            errs.append(('t not p^f', i, p, t))
    if s * s != k + l * (v - 1): errs.append(('s', i))
    if s < 0: errs.append(('s negative', i))
missing = sorted(set(target) - set(rows), key=lambda x: int(x[1:]))
print('target rows not in parts:', len(missing))
# settle tsv
seen = set()
for line in open(os.path.join(P, 'scratch/settle-i13.tsv'), encoding='utf-8'):
    a = line.rstrip('\n').split('\t')
    i, st, ev, ln = a
    pm = re.search(r'Part(\d+)$', ev)
    if i in seen: errs.append(('tsv dup', i))
    seen.add(i)
    if i not in rows: errs.append(('tsv row not in parts', i)); continue
    if int(pm[1]) != where[i]: errs.append(('tsv part', i, pm[1], where[i]))
    if ln != f'SignedDifferenceSets.OrbitRows.n{i[1:]}_not_hasSDS': errs.append(('tsv thm', i, ln))
    if st != 'none': errs.append(('tsv status', i, st))
if seen != set(rows): errs.append(('tsv vs parts', len(seen), len(rows)))
print('errors:', len(errs))
for e in errs[:40]: print(e)
open(os.path.join(P, 'reviews/R26/missing.txt'), 'w').write('\n'.join(missing) + '\n')
