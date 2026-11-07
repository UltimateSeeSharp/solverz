# Independent check: each row theorem of Parts 95-98 matches its instances.csv key and the row is open.
import csv, re, sys, os
base = os.path.dirname(os.path.abspath(__file__))
prob = os.path.normpath(os.path.join(base, '..', '..', '..'))
rows = {r['id']: r for r in csv.DictReader(open(os.path.join(prob, 'instances.csv'), encoding='utf-8'))}
pat = re.compile(r'theorem n(\d+)_not_hasSDS : ¬ HasSDS \(([^)]*)\) (\S+) (\S+) :=')
seen = []
for part in (95, 96, 97, 98):
    txt = open(os.path.join(prob, 'lean/SignedDifferenceSets/CosetRows/Part%d.lean' % part), encoding='utf-8').read()
    for m in pat.finditer(txt):
        nid = 'N' + m.group(1)
        grp = m.group(2)
        fac = [int(x) for x in re.findall(r'ZMod (\d+)', grp)]
        k, lam = int(m.group(3)), int(m.group(4).strip('()'))
        key = rows[nid]['key']
        km = re.match(r'SDS\((\d+),(-?\d+),(-?\d+),\[([\d,]+)\]\)', key)
        v, kk, ll = int(km.group(1)), int(km.group(2)), int(km.group(3))
        kf = [int(x) for x in km.group(4).split(',')]
        prod = 1
        for f in fac: prod *= f
        ok = (fac == kf and kk == k and ll == lam and prod == v and grp.count('ZMod') == len(fac))
        seen.append(nid)
        print(part, nid, grp, k, lam, key, rows[nid]['status'], 'OK' if ok else 'MISMATCH')
print(len(seen), 'rows;', len(set(seen)), 'distinct')
tg = [l.split('\t')[0] for l in open(os.path.join(prob, 'scratch/agentY/targets.tsv')) if l.strip()]
print('targets not in parts:', set(tg) - set(seen), 'parts not in targets:', set(seen) - set(tg))
