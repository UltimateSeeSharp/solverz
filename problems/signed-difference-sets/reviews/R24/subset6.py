import csv
from collections import Counter
from rows6 import parse, lean_rule, c22_rule, isqrt_exact, vp
rows = list(csv.DictReader(open('instances-2592b7a.csv', encoding='utf-8')))
bad = 0; why = Counter(); ex = 0
for r in rows:
    v, k, lam, ms = parse(r['key'])
    L = bool(lean_rule(v, k, lam, ms)); C = c22_rule(v, k, lam, ms)
    if r['status'] == 'exists': ex += 1
    if L and not C: bad += 1; print('LEAN-ONLY', r['id'], r['key'])
    if C and not L and r['status'] == 'open':
        n = k - lam; s = isqrt_exact(k + lam * (v - 1))
        big = [p for p in range(2, v + 1) if v % p == 0 and all(p % d for d in range(2, p)) and p > 19]
        tag = 'p2-nonsquare' if v % 2 == 0 and isqrt_exact(n) is None else ('prime>19' if big else 'p2-equality/other')
        why[tag] += 1
print('lean-only rows', bad, 'exists rows', ex, 'C22-only open rows by reason', dict(why))
