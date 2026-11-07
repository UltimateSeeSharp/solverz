import sys, csv, math, re
sys.path.insert(0, sys.argv[2])
import orbitrows as o
inst = {r['id']: r for r in csv.DictReader(open('instances.csv', encoding='utf-8'))}
miss = open('reviews/R26/missing.txt').read().split()
small = []
for i in miss:
    m = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)', inst[i]['key'])
    v, k, lam = map(int, m.groups()[:3]); shape = [int(x) for x in m[4].split(',')]
    n = k - lam; s = math.isqrt(k + lam * (v - 1))
    t = o.generator(shape, n); sizes = o.orbit_sizes(shape, t)
    lv = o.leaves(tuple(sizes), (k + s) // 2, (k - s) // 2)
    if lv <= 1500: small.append((i, inst[i]['key'], t, s, lv, len(sizes)))
print(len(miss), 'missing;', len(small), 'with <= 1500 leaves')
for x in small: print(x)
