"""A3 recomputed: v odd, lam even, d = v - k, d(d-1) < v - 1. Compare with ideator's sp_hits.txt; list
statuses hit; brute-force the parity lemma on small groups."""
import sys, itertools, collections; sys.path.insert(0, '.')
from common import *
I = instances()
hit = {i: (key, st) for i, key, st, v, k, lam, sh in I if v % 2 and lam % 2 == 0 and (v - k) * (v - k - 1) < v - 1}
print('hits by status', collections.Counter(st for key, st in hit.values()))
theirs = {l.split()[0] for l in open(IDEA + '/sp_hits.txt')}
mine_open = {i for i, (key, st) in hit.items() if st == 'open'}
print('open hits mine', len(mine_open), 'theirs', len(theirs), 'diff', sorted(mine_open ^ theirs)[:10])
print('exists hit:', [(i, key) for i, (key, st) in hit.items() if st == 'exists'])
print('none-status hit (already known nonexistent):', sum(st == 'none' for key, st in hit.values()))
# v even & lam odd anywhere?
print('v even, lam odd rows by status', collections.Counter(st for i, key, st, v, k, lam, sh in I if v % 2 == 0 and lam % 2))
print('d range of open hits', collections.Counter(next(v - k for j, key, st, v, k, lam, sh in I if j == i) for i in mine_open).most_common(30))
