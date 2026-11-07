import csv, re, math
from math import gcd
def sqf(n):
    d = 2
    while d * d <= n:
        if n % (d * d) == 0: return False
        d += 1
    return True
objs = {}
for line in open('objects/_objects.md', encoding='utf-8'):
    c = line.split('|')
    if len(c) > 5 and re.fullmatch(r'\s*O\d+\s*', c[1]):
        for nid in re.findall(r'N\d+', c[4]): objs[nid] = c[1].strip()
res = {}
for fn in ('scratch/e10.out', 'scratch/e11.out'):
    for line in open(fn):
        a = line.split(); res[a[0]] = a[2]
for r in csv.DictReader(open('instances.csv', encoding='utf-8')):
    m = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)', r['key'])
    v, k, l = int(m[1]), int(m[2]), int(m[3]); n = k - l
    if (r['status'] == 'exists' or r['id'] in objs) and n > 0 and gcd(v, n) == 1:
        print(r['id'], r['key'], r['status'], 'n=%d' % n, 'sqf' if sqf(n) else 'NONSQF', objs.get(r['id'], '-'), res.get(r['id'], '-'), r['evidence'][:50])
