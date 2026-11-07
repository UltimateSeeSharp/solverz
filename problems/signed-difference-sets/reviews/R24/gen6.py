"""Generate R6Check.lean: chunk key lists from instances.csv (ids from the tsv, keys from the csv), axioms, examples."""
import csv
from rows6 import parse
st = {r['id']: r for r in csv.DictReader(open('../../../instances.csv', encoding='utf-8'))}
tsv = [l.rstrip('\n').split('\t') for l in open('../../settle-c22.tsv', encoding='utf-8')]
by = {}
for rid, _, ch, _ in tsv: by.setdefault(int(ch.split()[-1]), []).append(rid)
out = ['import SignedDifferenceSets.SylowRows', '', 'open SignedDifferenceSets', '']
for th in ['not_hasSDS_of_sylow', 'SyCert.not_hasSDS'] + [f'sylowRows{c}_not_hasSDS' for c in range(1, 7)] + \
          [f'sylowRows{c}_kill' for c in range(1, 7)] + ['MaRows.cycloFacts_of_mem_maPairs']:
    out.append(f'#print axioms SignedDifferenceSets.{th}')
out.append('#check @SignedDifferenceSets.not_hasSDS_of_sylow')
def lit(rid):
    v, k, lam, ms = parse(st[rid]['key'])
    return f'({rid[1:]}, {ms}, {k}, ({lam} : ℤ))', ms, k, lam
for c in sorted(by):
    items = ',\n  '.join(lit(r)[0] for r in by[c])
    out += ['', 'set_option maxRecDepth 100000 in',
            f'example : sylowRows{c}.map (fun x => (x.1.id, x.1.ms, x.1.k, x.1.lam)) =\n  [{items}] := by decide +kernel']
def ty(ms): return ' × '.join(f'ZMod {m}' for m in ms)
L = open('../../../lean/SignedDifferenceSets/SylowRows.lean', encoding='utf-8').read()
import re
for rid in ['N1539', 'N4738', 'N69793', 'N65146', 'N69850']:
    _, ms, k, lam = lit(rid)
    m = re.search(r'\(⟨' + rid[1:] + r', \[[^\]]*\], \d+, -?\d+⟩,\s*(⟨[^⟩]*⟩)\)', L)
    c = [ch for ch in by if rid in by[ch]][0]
    out += ['', f'-- {rid}: {st[rid]["key"]}', f'example : ¬ HasSDS ({ty(ms)}) {k} ({lam}) :=',
            f'  sylowRows{c}_not_hasSDS (x := (⟨{rid[1:]}, {ms}, {k}, {lam}⟩, {m[1]})) (by decide +kernel) inferInstance']
open('R6Check.lean', 'w', encoding='utf-8').write('\n'.join(out) + '\n')
# controls: each must fail
ctl = ['import SignedDifferenceSets.SylowRows', '', 'open SignedDifferenceSets', '',
 '-- C1 wrong k: must fail', 'example : ¬ HasSDS (ZMod 88) 79 (14) :=',
 '  sylowRows1_not_hasSDS (x := (⟨1539, [88], 78, 14⟩, ⟨2, 4, 6, 2, 3, 36, [8]⟩)) (by decide +kernel) inferInstance',
 '-- C2 an existing SDS (O13, C2 x C16, (32,20,4), s = 12): Kills must be false', 'example : SyCert.Kills ⟨0, [2, 16], 20, 4⟩ ⟨2, 8, 4, 1, 5, 12, [2, 16]⟩ := by decide +kernel',
 '-- C3 q one too big for e (2(qφ+1) ≤ eφ fails): must fail', 'example : SyCert.Kills ⟨1539, [88], 78, 14⟩ ⟨2, 4, 6, 3, 3, 36, [8]⟩ := by decide +kernel',
 '-- C4 (2,3) not in maPairs, ds [8] with r = 3: must fail', 'example : SyCert.Kills ⟨1539, [88], 78, 14⟩ ⟨2, 3, 6, 2, 3, 36, [8]⟩ := by decide +kernel',
 '-- C5 quotient not a p-power (ds [4,1] ok but [6]): must fail', 'example : SyCert.Kills ⟨0, [12], 11, 2⟩ ⟨2, 2, 0, 0, 1, 3, [6]⟩ := by decide +kernel',
 '-- C6 positive control: the real cert of N1539 is decided true', 'example : SyCert.Kills ⟨1539, [88], 78, 14⟩ ⟨2, 4, 6, 2, 3, 36, [8]⟩ := by decide +kernel']
open('R6Control.lean', 'w', encoding='utf-8').write('\n'.join(ctl) + '\n')
print('ok', {c: len(by[c]) for c in by})
