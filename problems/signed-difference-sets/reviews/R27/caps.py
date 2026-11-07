"""Refuter A7: rerun the capped (row, H, t) of exists.out with c > 1 at a 5M-leaf cap, rows without an object."""
obj = set(open("objids.txt").read().split())
import re, time
from search import search
for l in open('exists.out'):
    m = re.match(r'(N\d+) \[([\d, ]*)\] \((\d+), (\d+), (-?\d+)\) H \[([\d, ]*)\] c (\d+) t (\d+) cap', l)
    if not m or int(m.group(7)) == 1 or m.group(1) in obj: continue
    rid, ms, v, k, lam, ds, c, t = m.groups()
    v, k, lam, c, t = int(v), int(k), int(lam), int(c), int(t)
    ds = [int(x) for x in ds.split(',')]
    s = int(round((k + lam * (v - 1)) ** 0.5))
    t0 = time.time()
    res, leaves, _ = search(ds, c, k, lam, t, s, cap=5_000_000)
    print(rid, (v, k, lam), 'H', ds, 'c', c, 't', t, res, leaves, f'{time.time() - t0:.0f}s', flush=True)
