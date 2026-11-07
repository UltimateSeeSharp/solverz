"""For each settled row, look for rows with the same (v,k,lam) on an isomorphic group (or any group) with status exists."""
import csv, re, os, sys
from collections import defaultdict
PF = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
def factor(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def canon(ms):
    parts = defaultdict(list)
    for m in ms:
        for p, e in factor(m).items(): parts[p].append(e)
    return tuple(sorted((p, tuple(sorted(es))) for p, es in parts.items()))
rows = {}
by = defaultdict(list)
for row in csv.DictReader(open(os.path.join(PF, 'instances.csv'), encoding='utf-8')):
    m = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]*)\]\)', row['key'])
    v, k, lam = int(m[1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(',')] if m[4] else []
    i = int(row['id'][1:]); rows[i] = (v, k, lam, ms, row['status'])
    by[(v, k, lam)].append(i)
ids = [int(l.split('\t')[0][1:]) for l in open(os.path.join(PF, 'scratch', 'settle-round2.tsv'), encoding='utf-8')]
iso_dup = 0; same_vkl_exists = 0
for i in ids:
    v, k, lam, ms, st = rows[i]
    for j in by[(v, k, lam)]:
        if j == i: continue
        if canon(rows[j][3]) == canon(ms):
            iso_dup += 1; print('ISO DUP', i, ms, j, rows[j][3], rows[j][4])
        elif rows[j][4] == 'exists':
            same_vkl_exists += 1
            if same_vkl_exists <= 10: print('same vkl exists in other group', i, ms, j, rows[j][3])
print('iso dups', iso_dup, 'same-vkl exists elsewhere', same_vkl_exists)
