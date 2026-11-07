"""Compare my kill sets with the scripts' outputs; union count beyond (E8, SC, A3, A5, A7)."""
import sys, glob, ast, collections
sys.path.insert(0, '.')
from xcommon import rows, SCR
R = rows(); st = {r['id']: r['status'] for r in R}
op = {i for i, s in st.items() if s == 'open'}
mine = {}
for f in glob.glob('xrun_*.out'):
    for l in open(f, encoding='utf-8'):
        head, *res = l.rstrip('\n').replace('|V|', 'nV').split('|')
        mine[head.split()[0]] = res
print('rows done:', len(mine), 'of', len(R))
M = {name: {i for i, r in mine.items() if r[j] != '-' and not r[j].startswith('unsure')}
     for j, name in enumerate(['SC', 'A1', 'SCpp', 'A2'])}
uns = {name: {i for i, r in mine.items() if r[j].startswith('unsure')} for j, name in enumerate(['SC', 'A1', 'SCpp', 'A2'])}
print('unsure:', {k: len(v) for k, v in uns.items()})
for name, S in M.items():
    print(f'mine {name}: by status', dict(collections.Counter(st[i] for i in S)))
# theirs
sc_th = {l.split()[0] for l in open(SCR + '/refuter/rule-sc/kills_indep.txt')}
scpp_th = {l.split()[0] for l in open(SCR + '/refuter/rule-sc/sc2_all.out') if l.split()[-1] != 'open' and not l.rstrip().endswith(' open')}
scpp_th = set()
for l in open(SCR + '/refuter/rule-sc/sc2_all.out', encoding='utf-8'):
    t = l.split()
    if t[3] != 'open': scpp_th.add(t[0])
tiers = {l.split()[0]: int(l.split()[2]) for l in open(SCR + '/ideator/tiers.txt')}
a1_th = {i for i, t in tiers.items() if t > 0}
a2_th = {l.split()[0] for l in open(SCR + '/ideator/m4_hits.txt')}
def cmp(name, mineS, theirs, scope):
    a, b = mineS & scope, theirs & scope
    print(f'{name}: mine {len(a)} theirs {len(b)} only-mine {len(a - b)} only-theirs {len(b - a)}',
          sorted(a - b)[:8], sorted(b - a)[:8])
done = set(mine)
cmp('SC (all rows)', M['SC'], sc_th, done)
cmp('SC++ (all rows)', M['SCpp'], scpp_th, done)
cmp('A1 (open)', M['A1'], a1_th, op & done)
t0 = {i for i, t in tiers.items() if t == 0}
cmp('A2 (open, A1 tier 0)', M['A2'], a2_th, t0 & done)
# base sets
E8 = set()
for l in open(SCR + '/e8/combined.out', encoding='utf-8'):
    t = l.split()
    if len(t) > 3 and t[3] == 'KILL': E8.add(t[0])
A3 = {l.split()[0] for l in open(SCR + '/ideator/sp_hits.txt')}
A5 = {x.split()[0] for f in glob.glob(SCR + '/ideator/oe_*.out') for x in open(f) if x.split()[3] == 'none'}
A7 = set()
for f in glob.glob(SCR + '/ideator/mc_*.out') + glob.glob(SCR + '/ideator/mcb_*.out'):
    for l in open(f):
        x = l.split(None, 2)
        if ast.literal_eval(x[2].strip())[0] == 'KILL': A7.add(x[0])
base = (E8 | sc_th | A3 | A5 | A7) & op
print('base sizes (open):', {n: len(s & op) for n, s in [('E8', E8), ('SC', sc_th), ('A3', A3), ('A5', A5), ('A7', A7)]}, 'union', len(base))
ext_th = (scpp_th | a1_th | a2_th) & op
ext_mine = (M['SCpp'] | M['A1'] | M['A2']) & op
print('extensions union (open): theirs', len(ext_th), 'mine', len(ext_mine))
print('new beyond base: theirs', len(ext_th - base), 'mine', len(ext_mine - base))
for name, S in [('SC++', scpp_th), ('A1', a1_th), ('A2', a2_th)]:
    print(f'  {name} alone beyond base (theirs):', len((S & op) - base))
for name in ['SCpp', 'A1', 'A2']:
    print(f'  {name} alone beyond base (mine):', len((M[name] & op) - base))
print('A1 - SC++ (open, theirs):', len((a1_th - scpp_th) & op), ' A2 - SC++:', len((a2_th - scpp_th) & op),
      ' A1 - SC++ (mine):', len((M['A1'] - M['SCpp']) & op), ' A2 - SC++ (mine):', len((M['A2'] - M['SCpp']) & op))
print('SC++ - (A1 u A2) (theirs):', len((scpp_th - a1_th - a2_th) & op))
open('new_kills.txt', 'w').write(''.join(f'{i}\n' for i in sorted(ext_mine - base, key=lambda x: int(x[1:]))))
b2 = base | (scpp_th & op)
print('A2 beyond base u SC++ (theirs):', len((a2_th & op) - b2), ' A1 beyond base u SC++:', len((a1_th & op) - b2))
print('total open killed by base u extensions:', len(base | ext_th))
