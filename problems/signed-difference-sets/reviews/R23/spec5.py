"""Append per-instance specialisations to R5Check.lean: the row's raw tuple from the part source,
the statement written with the plain product of ZMod from instances.csv."""
import re, os
exec(open('reviews/R23/rows5.py', encoding='utf-8').read().split('# check each part row')[0].replace('ROOT = sys.argv[1]', 'ROOT = os.getcwd()'))
neg = [rid for rid, x in part.items() if x[3] < 0]
big = max(part, key=lambda r: byid[r][0])
many = max(part, key=lambda r: len(part[r][1]))
picks = [168, 930, 571, 7151, big, many] + neg[:2]
print('neg-lambda rows', len(neg), neg[:5], 'big', big, byid[big][:4], 'many', many, byid[many][:4])
out = []
for rid in picks:
    nn = part[rid][0]
    src = re.sub(r'\s+', ' ', open(os.path.join(LEAN, f'Part{nn:02d}.lean'), encoding='utf-8').read())
    m = re.search(r'\(⟨' + str(rid) + r', \[.*?\]\]⟩\)', src)
    v, k, lam, ms, *_ = byid[rid]
    G = ' × '.join(f'ZMod {x}' for x in ms)
    out.append(f'\n-- N{rid}: {v},{k},{lam},{ms}\nexample : ¬ HasSDS ({G}) {k} ({lam}) :=\n  not_hasSDS_of_mem_part{nn:02d} (x := {m[0]}) (by decide +kernel) inferInstance')
open('reviews/R23/R5Check.lean', 'a', encoding='utf-8').write('\n'.join(out) + '\n')
