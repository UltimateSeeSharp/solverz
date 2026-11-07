"""Generate R5Check.lean: kernel-checked equality of each part's (id, ms, k, lam) with instances.csv
(rows taken in the order of my own sorted id list per part), axioms, and per-instance specialisations."""
import csv, re, sys, os
exec(open('reviews/R23/rows5.py', encoding='utf-8').read().split('# check each part row')[0].replace('ROOT = sys.argv[1]', 'ROOT = os.getcwd()'))
out = ['import SignedDifferenceSets.MaRows.All', '', 'open SignedDifferenceSets SignedDifferenceSets.MaRows', '']
for th in ['SignedDifferenceSets.maRule'] + [f'SignedDifferenceSets.MaRows.not_hasSDS_of_mem_part{n:02d}' for n in range(1, 7)] + \
        ['SignedDifferenceSets.MaRows.not_hasSDS_of_mem_maRows', 'SignedDifferenceSets.MaRows.part03_kills',
         'SignedDifferenceSets.CycloFacts.mul', 'SignedDifferenceSets.MaRows.cycloFacts_of_mem_maPairs']:
    out.append(f'#print axioms {th}')
out.append('#check @SignedDifferenceSets.MaRows.not_hasSDS_of_mem_part01')
out.append('#print SignedDifferenceSets.MaRule')
# kernel equality per part, in the part's own order (from source parse order), values from instances.csv
order = {}
for nn in range(1, 7):
    src = re.sub(r'\s+', ' ', open(os.path.join(LEAN, f'Part{nn:02d}.lean'), encoding='utf-8').read())
    order[nn] = [int(x) for x in re.findall(r'\(⟨(\d+), \[', src)]
for nn in range(1, 7):
    items = []
    for rid in order[nn]:
        v, k, lam, ms, st, lean, ev = byid[rid]
        assert st == 'open'
        items.append(f'({rid}, {ms}, {k}, {lam})'.replace(' -', ' -'))
    out.append(f'\nset_option maxRecDepth 100000 in\nexample : part{nn:02d}.map (fun x => (x.1.id, x.1.ms, x.1.k, x.1.lam)) = ')
    out.append('  [' + ',\n   '.join(items) + '] := by decide +kernel')
open('reviews/R23/R5Check.lean', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print('written', sum(len(v) for v in order.values()))
