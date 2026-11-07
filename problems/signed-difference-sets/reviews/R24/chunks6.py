"""Parse SylowRows.lean; compare (id, ms, k, lam) with instances.csv keys; re-check Kills in Python."""
import csv, re, math, glob
from rows6 import parse, vp
L = open('../../../lean/SignedDifferenceSets/SylowRows.lean', encoding='utf-8').read()
chunks = re.split(r'def sylowRows(\d+) : List \(Row × SyCert\) := \[', L)
ent = {}
pat = re.compile(r'\(⟨(\d+), \[([\d, ]+)\], (\d+), (-?\d+)⟩,\s*⟨(\d+), (\d+), (\d+), (\d+), (\d+), (-?\d+), \[([\d, ]+)\]⟩\)')
for i in range(1, len(chunks), 2):
    c = int(chunks[i]); body = chunks[i + 1].split('theorem')[0]
    es = pat.findall(body)
    assert body.count('(⟨') == len(es), (c, body.count('(⟨'), len(es))
    for e in es:
        rid = 'N' + e[0]; assert rid not in ent
        ent[rid] = (c, [int(x) for x in e[1].split(',')], int(e[2]), int(e[3]),
                    tuple(int(x) for x in e[4:10]), [int(x) for x in e[10].split(',')])
print('entries', len(ent), 'chunks', sorted({x[0] for x in ent.values()}))
for name, path in [('2592b7a', 'instances-2592b7a.csv'), ('now', '../../../instances.csv')]:
    st = {r['id']: r for r in csv.DictReader(open(path, encoding='utf-8'))}
    mism = 0; stc = {}
    for rid, (c, ms, k, lam, cert, ds) in ent.items():
        v2, k2, l2, ms2 = parse(st[rid]['key'])
        if (ms, k, lam) != (ms2, k2, l2): mism += 1; print('MISMATCH', rid)
        stc[st[rid]['status']] = stc.get(st[rid]['status'], 0) + 1
    print(name, 'key mismatches', mism, 'statuses', stc)
tsv = [l.rstrip('\n').split('\t') for l in open('../../settle-c22.tsv', encoding='utf-8')]
bad = [t for t in tsv if t[0] not in ent or t[1] != 'none' or t[2] != f'C22; SylowRows chunk {ent[t[0]][0]}'
       or t[3] != f'SignedDifferenceSets.sylowRows{ent[t[0]][0]}_not_hasSDS']
print('tsv lines', len(tsv), 'bad', len(bad), bad[:3], 'set equal', set(t[0] for t in tsv) == set(ent))
def isprime(p): return p >= 2 and all(p % d for d in range(2, p))
PAIRS = {(2,1),(2,2),(2,4),(2,8),(2,16),(2,32),(2,64),(2,128),(3,1),(3,3),(3,9),(3,27),(3,81),(5,1),(5,5),
         (5,25),(7,1),(7,7),(7,49),(11,1),(11,11),(13,1),(13,13),(17,1),(19,1)}
fails = 0; dist = {}
for rid, (c, ms, k, lam, (p, r, e, q, t, s), ds) in ent.items():
    ok = (isprime(p) and r > 0 and all(m > 0 for m in ms) and len(ds) == len(ms)
          and all(m % d == 0 for d, m in zip(ds, ms))
          and all(d > 0 and (r * p) % d == 0 and p ** vp(d, p) == d for d in ds)
          and (k - lam) % p ** e == 0 and 2 * (q * ((p - 1) * r) + 1) <= e * ((p - 1) * r)
          and math.prod(ds) == p ** t and s * s == k + lam * (math.prod(ms) - 1)
          and s % p ** min(t, q + 1) != 0 and (p, r) in PAIRS)
    # the quotient must be the full Sylow p-part capped by r p (informational)
    if not ok: fails += 1; print('KILLS FAILS', rid)
    dist[(p, r)] = dist.get((p, r), 0) + 1
print('my Kills fails', fails, 'pairs used', dict(sorted(dist.items())))
# objects: no object's instance in the batch
md = open('../../../objects/_objects.md', encoding='utf-8').read()
objinst = set(re.findall(r'\|\s*(N\d+)\s*\|', md))
print('object instances', len(objinst), 'in batch', objinst & set(ent))
