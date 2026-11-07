"""Does A1 ever kill an open row only through an odd-exponent triple (b = ceil(e/2) > floor(e/2))?
And: odd-exponent triples on open rows at all (He-Wu Thm 3.2 should have removed them)."""
import sys, collections
sys.path.insert(0, '.')
from xcommon import rows, parse
from xrules import triples
st = collections.Counter(); ex = []
for r in rows():
    if r['status'] != 'open': continue
    v, k, lam, sh = parse(r['key'])
    odd = even = False
    for p, e, h, m, c in triples(v, k, lam, sh, emin=1):
        b = (e + 1) // 2
        kill = p ** b > 2 * c or (c == 1 and p ** b == 2 and k < v)
        if e % 2: st['odd-e triples'] += 1; odd |= kill
        else: even |= kill
    if odd: st['rows with odd-e kill'] += 1
    if odd and not even: st['rows killed only via odd e'] += 1; ex.append(r['key'])
    if v < 9: st['open v<9'] += 1
print(dict(st), ex[:10])
