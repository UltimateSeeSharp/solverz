import csv, re, sys, math
from math import gcd
def sqf(n):
    d = 2
    while d * d <= n:
        if n % (d * d) == 0: return False
        d += 1
    return True
res = {}
for fn in ('scratch/e10.out', 'scratch/e11.out'):
    for line in open(fn):
        a = line.split(); res[a[0]] = a[2]
for f in sys.argv[1:]:
    t = set()
    for r in csv.DictReader(open(f, encoding='utf-8')):
        m = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)', r['key'])
        v, k, l = int(m[1]), int(m[2]), int(m[3]); n = k - l
        if r['status'] == 'open' and res.get(r['id']) == 'none' and n > 0 and gcd(v, n) == 1 and not sqf(n): t.add(r['id'])
    print(f, len(t))
