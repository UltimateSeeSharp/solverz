"""Refuter A7: parse CosetRows parts, check each row against instances.csv, the batch, I13, objects,
and the side conditions (own arithmetic). Writes rows.json for search.py."""
import csv, glob, json, math, os, re, sys
P = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
LEAN = os.path.join(P, 'lean', 'SignedDifferenceSets', 'CosetRows')
thm_re = re.compile(r'theorem n(\d+)_not_hasSDS : ¬ HasSDS \(([^)]*)\) (-?\d+|\(-\d+\)) (-?\d+|\(-\d+\)) :=\s*\n'
                    r'\s*not_hasSDS_of_cosetRow(\'?) \(ms := \[([\d, ]*)\]\) \(ds := \[([\d, ]*)\]\) '
                    r'\(c := (\d+)\) \(t := (\d+)\) \(s := (-?\d+)\)')
def ints(s): return [int(x) for x in s.split(',') if x.strip()]
def num(s): return int(s.strip('()'))
rows = {}
nthm = 0
for f in sorted(glob.glob(os.path.join(LEAN, 'Part*.lean'))):
    part = os.path.basename(f)[:-5]
    txt = open(f, encoding='utf-8').read()
    nthm += txt.count('_not_hasSDS :')
    for m in thm_re.finditer(txt):
        i, grp, k, lam, prime, ms, ds, c, t, s = m.groups()
        g = [int(x) for x in re.findall(r'ZMod (\d+)', grp)]
        assert grp == ' × '.join(f'ZMod {x}' for x in g), grp
        rid = 'N' + i
        assert rid not in rows, rid
        rows[rid] = dict(id=rid, part=part, grp=g, k=num(k), lam=num(lam), witt=bool(prime), ms=ints(ms),
                         ds=ints(ds), c=int(c), t=int(t), s=int(s),
                         split=('cosetSearch_of_slices' in txt[m.end():m.end() + 400].split('theorem')[0]))
print('theorems', nthm, 'parsed', len(rows))
inst = {r['id']: r for r in csv.DictReader(open(os.path.join(P, 'instances.csv'), encoding='utf-8'))}
key_re = re.compile(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]*)\]\)')
batch = [l.rstrip('\n').split('\t') for l in open(os.path.join(P, 'scratch', 'settle-a7.tsv'), encoding='utf-8') if l.strip()]
i13 = {l.split('\t')[0] for l in open(os.path.join(P, 'scratch', 'settle-i13.tsv'), encoding='utf-8') if l.strip()}
objtxt = open(os.path.join(P, 'objects', '_objects.md'), encoding='utf-8').read()
obj_ids = set(re.findall(r'\|\s*(N\d+)\s*\|', objtxt))
def isprime(p): return p > 1 and all(p % q for q in range(2, math.isqrt(p) + 1))
def pf(n): return [p for p in range(2, n + 1) if n % p == 0 and isprime(p)]
def sqfree(n): return all(n % (p * p) for p in pf(n))
bad = []
seen = set()
for b in batch:
    rid, st, src, name = b
    if rid in seen: bad.append((rid, 'dup in batch'))
    seen.add(rid)
    r = rows.get(rid)
    if r is None: bad.append((rid, 'no theorem')); continue
    if st != 'none': bad.append((rid, 'status ' + st))
    if not src.endswith(r['part']): bad.append((rid, 'part ' + src))
    if name != f'SignedDifferenceSets.CosetRows.n{rid[1:]}_not_hasSDS': bad.append((rid, 'name'))
    if rid in i13: bad.append((rid, 'in i13'))
    if rid in obj_ids: bad.append((rid, 'object'))
    I = inst[rid]
    if I['status'] != 'open' or I['evidence'] or I['lean'] or I['solution']:
        bad.append((rid, 'inst ' + str([I['status'], I['evidence'], I['lean'], I['solution']])))
    v, k, lam, fac = key_re.fullmatch(I['key']).groups()
    v, k, lam, fac = int(v), int(k), int(lam), ints(fac)
    if (fac, k, lam) != (r['grp'], r['k'], r['lam']) or r['ms'] != r['grp'] or math.prod(fac) != v:
        bad.append((rid, 'key ' + I['key'] + ' vs ' + str((r['grp'], r['ms'], r['k'], r['lam']))))
    ms, ds, c, t, s = r['ms'], r['ds'], r['c'], r['t'], r['s']
    n = k - lam
    H = math.prod(ds)
    ok = (len(ms) == len(ds) and all(d >= 1 and m % d == 0 for d, m in zip(ds, ms)) and math.prod(ms) == c * H
          and n > 0 and math.gcd(H, n) == 1 and math.gcd(t, H) == 1 and s * s == k + lam * (v - 1))
    if not ok: bad.append((rid, 'side'))
    for p in pf(n):
        e = math.lcm(*ds) if ds else 1
        if not any(all(t % d == pow(p, f, d) % d if d > 1 else True for d in ds) for f in range(max(e, 1) * 2)):
            bad.append((rid, f'p={p}'))
    if r['witt'] == sqfree(n) and not (r['witt'] and not sqfree(n)):
        if not r['witt'] and not sqfree(n): bad.append((rid, 'C16 on non-squarefree'))
    if not r['witt'] and not sqfree(n): bad.append((rid, 'C16 on non-squarefree'))
    r.update(n=n, H=H, v=v, sqfree=sqfree(n), inbatch=True)
extra = sorted(set(rows) - seen)
print('batch', len(batch), 'distinct', len(seen), 'theorems not in batch', extra)
print('problems', len(bad)); [print(x) for x in bad[:40]]
import collections
print('c=1 rows (H = G):', [r['id'] for r in rows.values() if r.get('inbatch') and r['c'] == 1][:20],
      sum(1 for r in rows.values() if r.get('inbatch') and r['c'] == 1))
print('witt rows:', sum(r['witt'] for r in rows.values() if r.get('inbatch')),
      'sqfree n among witt:', sum(r['witt'] and r['sqfree'] for r in rows.values() if r.get('inbatch')))
json.dump([r for r in rows.values() if r.get('inbatch')], open(os.path.join(os.path.dirname(__file__), 'rows.json'), 'w'))
