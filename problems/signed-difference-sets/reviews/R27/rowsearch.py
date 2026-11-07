"""Refuter A7, check 3: own search on every batch row's named quotient and t; appends to rowsearch.out
(id part result leaves seconds); skips ids already there. Usage: python rowsearch.py <slot> <nslots>."""
import json, os, sys, time
from search import search
D = os.path.dirname(os.path.abspath(__file__))
slot, nslots = int(sys.argv[1]), int(sys.argv[2])
R = json.load(open(os.path.join(D, 'rows.json')))
R.sort(key=lambda r: (r['H'] * (2 * r['c'] + 1), r['id']))
outf = os.path.join(D, f'rowsearch{slot}.out')
done = set()
if os.path.exists(outf):
    done = {l.split()[0] for l in open(outf) if l.strip()}
with open(outf, 'a') as fo:
    for j, r in enumerate(R):
        if j % nslots != slot or r['id'] in done: continue
        t0 = time.time()
        res, leaves, _ = search(r['ds'], r['c'], r['k'], r['lam'], r['t'], r['s'], cap=20_000_000)
        fo.write(f"{r['id']} {r['part']} {res} {leaves} {time.time() - t0:.1f}\n"); fo.flush()
