# Published families vs rows still 'open' in instances.csv (rows the corrections might have missed).
import csv, re, sys, collections
rows = list(csv.DictReader(open(sys.argv[1] + '/instances.csv', encoding='utf-8')))
def key(r):
    v, k, l, sh = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[(.*)\]\)", r['key']).groups()
    return int(v), int(k), int(l), tuple(int(x) for x in sh.split(','))
def pp(q):
    for p in range(2, q + 1):
        if q % p == 0:
            while q % p == 0: q //= p
            return (p if q == 1 else None)
by = collections.defaultdict(list)
for r in rows: v, k, l, sh = key(r); by[(v, k, l)].append((r['id'], sh, r['status'], r['source'][:4], r['evidence'][:30]))
def show(tag, t):
    for x in by.get(t, []): print(tag, t, x)
for q in range(3, 500):
    p = pp(q)
    if p and q % 4 == 3: n = (q + 1) // 4; show('Prop2.3', (q, 2 * n, n - 2))
for m in range(3, 13):
    q, r = 2 * m - 3, 2 * m + 3
    if pp(q) and pp(r) and q * r < 500: n = m * m; show('Thm4.1', (4 * n - 9, 2 * n - 1, n - 1))
for t in [(29, 8, 1), (61, 16, 3), (349, 88, 21)]: show('Thm3.2', t)
