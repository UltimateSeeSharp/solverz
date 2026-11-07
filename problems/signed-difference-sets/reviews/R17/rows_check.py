"""Cross-check the Lean row data of C17, C7 and the orbit rows against instances.csv and settle-round2.tsv."""
import csv, re, sys, glob, os
from math import prod
PF = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
L = os.path.join(PF, 'lean', 'SignedDifferenceSets')

inst = {}
for row in csv.DictReader(open(os.path.join(PF, 'instances.csv'), encoding='utf-8')):
    m = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]*)\]\)', row['key'])
    v, k, lam = int(m[1]), int(m[2]), int(m[3])
    ms = [int(x) for x in m[4].split(',')] if m[4] else []
    inst[int(row['id'][1:])] = dict(v=v, k=k, lam=lam, ms=ms, status=row['status'], lean=row['lean'], ev=row['evidence'])

def tup(s):
    return [int(x) for x in s.split(',')] if s.strip() else []

src = {}  # id -> list of (source, ms, k, lam)
txt = open(os.path.join(L, 'RealCharsRows.lean'), encoding='utf-8').read()
body = txt.split('def realCharsRows')[1].split('theorem realCharsRows_kill')[0]
for m in re.finditer(r'\(⟨(\d+), \[([\d, ]*)\], (\d+), (-?\d+)⟩, ⟨(\d+), (-?\d+), (-?\d+)⟩\)', body):
    src.setdefault(int(m[1]), []).append(('RC', tup(m[2]), int(m[3]), int(m[4]), (int(m[5]), int(m[6]), int(m[7]))))
nrc = sum(1 for v in src.values() for x in v if x[0] == 'RC')
for f in sorted(glob.glob(os.path.join(L, 'MarkedCountsRows', 'Part*.lean'))):
    part = 'MC' + os.path.basename(f)[4:6]
    t = open(f, encoding='utf-8').read()
    for m in re.finditer(r'\(⟨(\d+), \[([\d, ]*)\], (\d+), (-?\d+)⟩,', t):
        src.setdefault(int(m[1]), []).append((part, tup(m[2]), int(m[3]), int(m[4]), None))
orbit_ts = {}
for f in sorted(glob.glob(os.path.join(L, 'OrbitRows', 'Part*.lean'))):
    t = open(f, encoding='utf-8').read()
    pat = re.compile(r'theorem n(\d+)_not_hasSDS : ¬ HasSDS \(([^)]*)\) (\d+) \(?(-?\d+)\)? :=\s*\n\s*not_hasSDS_of_orbitRow \(ms := \[([\d, ]*)\]\) \(t := (\d+)\) \(s := \(?(-?\d+)\)?\)\s*\n\s*\(by decide \+kernel\) _')
    n_thm = len(re.findall(r'theorem n\d+_not_hasSDS', t))
    found = list(pat.finditer(t))
    if len(found) != n_thm:
        print('PARSE MISMATCH', f, n_thm, len(found))
    for m in found:
        grp = [int(x) for x in re.findall(r'ZMod (\d+)', m[2])]
        if ' × '.join(f'ZMod {g}' for g in grp) != m[2].strip():
            print('GROUP TEXT ODD', m[1], m[2])
        ms = tup(m[5])
        if grp != ms:
            print('GROUP != ms', m[1], grp, ms)
        src.setdefault(int(m[1]), []).append(('OR' + os.path.basename(f)[4:6], ms, int(m[3]), int(m[4]), (int(m[6]), int(m[7]))))
        orbit_ts[int(m[1])] = (ms, int(m[3]), int(m[4]), int(m[6]), int(m[7]))
print('RC rows', nrc, 'MC rows', sum(1 for v in src.values() for x in v if x[0].startswith('MC')), 'OR rows', len(orbit_ts))

bad = 0
for i, lst in src.items():
    if len(lst) > 1:
        print('MULTI', i, [x[0] for x in lst])
    r = inst.get(i)
    for (s, ms, k, lam, c) in lst:
        if r is None:
            print('NO ROW', i, s); bad += 1; continue
        if (ms, k, lam) != (r['ms'], r['k'], r['lam']) or prod(ms) != r['v']:
            print('DATA MISMATCH', i, s, ms, k, lam, r); bad += 1
        if r['status'] != 'open':
            print('NOT OPEN', i, s, r['status'], r['ev']); bad += 1
print('data mismatches/not-open', bad)

tsv = [l.rstrip('\n').split('\t') for l in open(os.path.join(PF, 'scratch', 'settle-round2.tsv'), encoding='utf-8')]
ids = [int(x[0][1:]) for x in tsv]
print('tsv rows', len(tsv), 'distinct', len(set(ids)))
for x in tsv:
    i = int(x[0][1:]); name = x[3]
    lst = src.get(i, [])
    srcs = [s[0] for s in lst]
    if name == 'SignedDifferenceSets.realCharsRows_not_hasSDS': ok = 'RC' in srcs
    elif 'MarkedCountsRows.part' in name: ok = ('MC' + name.split('part')[1][:2]) in srcs
    elif 'OrbitRows.n' in name: ok = name.endswith(f'.n{i}_not_hasSDS') and any(s.startswith('OR') for s in srcs)
    else: ok = False
    if not ok or x[1] != 'none': print('TSV BAD', x, srcs)
missing = set(src) - set(ids)
print('in Lean but not in tsv', sorted(missing)[:20], len(missing))
for i in sorted(missing):
    print('  ', i, [s[0] for s in src[i]], inst[i]['status'], inst[i]['ev'][:80])
