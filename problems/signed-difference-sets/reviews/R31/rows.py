"""Independent parse of OrbitRows Part60..137 against instances.csv, e10/e11 and objects (refuter xsplit)."""
import csv, re, os, math, sys, json
from math import gcd
P = sys.argv[1]
D = os.path.join(P, 'lean/SignedDifferenceSets/OrbitRows')
def parse_key(key):
    m = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)', key)
    v, k, l = int(m[1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(',')]
    assert math.prod(ms) == v; return v, k, l, ms
def factor(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
inst = {r['id']: r for r in csv.DictReader(open(os.path.join(P, 'instances.csv'), encoding='utf-8'))}
res = {}
for fn in ('scratch/e10.out', 'scratch/e11.out'):
    if not os.path.exists(os.path.join(P, fn)): print('missing', fn); continue
    for line in open(os.path.join(P, fn)):
        a = line.split()
        if a: res[a[0]] = a[2]
objs = set()
for line in open(os.path.join(P, 'objects/_objects.md'), encoding='utf-8'):
    c = line.split('|')
    if len(c) > 5 and re.fullmatch(r'\s*O\d+\s*', c[1]): objs.update(re.findall(r'N\d+', c[4]))
lam_re = r'(\(-\d+\)|\d+)'
li = lambda x: int(x.strip('()'))
thm = re.compile(r'theorem n(\d+)_not_hasSDS (?:: ¬ HasSDS \(([^)]*)\) (\d+) ' + lam_re + r' :=|\(inst : Fintype \(Grp \[([\d, ]+)\]\)\) :\s*¬ @HasSDS \(Grp \[([\d, ]+)\]\) _ inst (\d+) ' + lam_re + r' :=)\s*(not_hasSDS_of_orbitSlices' + "'?" + r') \(ms := \[([\d, ]+)\]\) \(t := (\d+)\) \(s := (\d+)\) \(by decide \+kernel\)\s*\(orbitExhaust_of_slices \(ms := \[([\d, ]+)\]\) \(k := (\d+)\) \(lam := ' + lam_re + r'\) \(t := (\d+)\)\s*\(s := (\d+)\) \(d := (\d+)\)\s*\[([\d,\s]+)\]\s*\(by decide \+kernel\) <\|((?:\s*\.cons n\d+_slice\d+ <\|)*)\s*\.single\) (inst|_)')
slc = re.compile(r'theorem n(\d+)_slice(\d+) : orbitSlice \[([\d, ]+)\] (\d+) ' + lam_re + r' (\d+) (\d+) (\d+) (\d+) (\d+) = true := by\s*decide \+kernel')
L = lambda s: [int(x) for x in s.replace(' ', '').split(',') if x]
slices, rows, bad = {}, [], []
for num in range(60, 138):
    f = os.path.join(D, f'Part{num:02d}.lean'); txt = open(f, encoding='utf-8').read()
    nthm = txt.count('theorem ')
    found = 0
    for m in slc.finditer(txt):
        found += 1
        key = (m[1], int(m[2])); assert key not in slices, key
        slices[key] = dict(part=num, ms=L(m[3]), k=int(m[4]), lam=li(m[5]), t=int(m[6]), s=int(m[7]), d=int(m[8]), a=int(m[9]), b=int(m[10]))
    for m in thm.finditer(txt):
        found += 1
        g = m.groups()
        nid = 'N' + g[0]
        if g[1] is not None:
            stmt_ms = [int(x.strip().split()[1]) for x in g[1].split('×')]; sk, sl = int(g[2]), li(g[3]); inst_form = False
        else:
            assert g[4] == g[5], nid; stmt_ms = L(g[4]); sk, sl = int(g[6]), li(g[7]); inst_form = True
        rows.append(dict(nid=nid, part=num, stmt_ms=stmt_ms, k=sk, lam=sl, rule=g[8], ms=L(g[9]), t=int(g[10]), s=int(g[11]),
                         ms2=L(g[12]), k2=int(g[13]), lam2=li(g[14]), t2=int(g[15]), s2=int(g[16]), d=int(g[17]), cuts=L(g[18]),
                         chain=re.findall(r'n(\d+)_slice(\d+)', g[19]), inst_form=inst_form, last=g[20]))
    if found != nthm: bad.append(('unparsed theorems', num, nthm, found))
    imps = re.findall(r'public import (\S+)', txt)
    if imps[0] != 'SignedDifferenceSets.OrbitSearchSplit' or any(not i.startswith('SignedDifferenceSets.OrbitRows.Part') for i in imps[1:]): bad.append(('imports', num, imps))
    for opt in re.findall(r'set_option (\S+ \S+)', txt):
        if opt not in ('maxRecDepth 100000', 'Elab.async false'): bad.append(('option', num, opt))
out = []
for r in rows:
    nid = r['nid']; ir = inst.get(nid); v, k, l, ms = parse_key(ir['key']); n = k - l
    sq = all(e == 1 for e in factor(n).values())
    err = []
    if not (r['stmt_ms'] == ms == r['ms'] == r['ms2']): err.append('ms')
    if not (r['k'] == k == r['k2'] and r['lam'] == l == r['lam2']): err.append('k/lam')
    if r['t'] != r['t2'] or r['s'] != r['s2']: err.append('t/s')
    if r['inst_form'] != (r['last'] == 'inst'): err.append('inst')
    if (r['rule'] == 'not_hasSDS_of_orbitSlices') != sq: err.append('rule')
    if r['s'] ** 2 != k + l * (v - 1): err.append('s2')
    if gcd(v, n) != 1 or gcd(r['t'], v) != 1 or n <= 0: err.append('gcd')
    for p in factor(n):
        if not any(all(r['t'] % m == pow(p, f, m) for m in ms) for f in range(v)): err.append(f't~{p}')
    # slices: chain = all slices of this row in order, params equal, contiguous cuts
    sl = sorted((i, s) for (x, i), s in slices.items() if x == nid[1:])
    if [int(i) for x, i in r['chain']] != list(range(len(sl))) or any(x != nid[1:] for x, _ in r['chain']): err.append('chain')
    cuts = [0] + r['cuts']
    for i, s in sl:
        if (s['ms'], s['k'], s['lam'], s['t'], s['s'], s['d']) != (ms, k, l, r['t'], r['s'], r['d']): err.append(f'slice{i}params')
        if (s['a'], s['b']) != (cuts[i], cuts[i + 1]): err.append(f'slice{i}cut')
        if s['part'] > r['part']: err.append(f'slice{i}after')
    if len(sl) != len(cuts) - 1: err.append('nslices')
    out.append(dict(nid=nid, part=r['part'], key=ir['key'], status=ir['status'], src=ir['source'], ev=ir['evidence'], lean=ir['lean'],
                    e10=res.get(nid), obj=nid in objs, sq=sq, t=r['t'], s=r['s'], d=r['d'], nsl=len(sl), end=cuts[-1], err=err))
print('bad:', bad)
print('rows:', len(out), 'slices:', len(slices), 'orphan slices:', sorted({x for x, _ in slices} - {r['nid'][1:] for r in out}))
for o in out: print(o['nid'], o['part'], o['key'], o['status'], o['src'], repr(o['ev']), repr(o['lean']), o['e10'], 'OBJ' if o['obj'] else '', 'sqf' if o['sq'] else 'nsq', 't=%d s=%d d=%d slices=%d end=%d' % (o['t'], o['s'], o['d'], o['nsl'], o['end']), 'ERR' + str(o['err']) if o['err'] else 'ok')
json.dump(out, open(os.path.join(P, 'reviews/R31/rows.json'), 'w'))
