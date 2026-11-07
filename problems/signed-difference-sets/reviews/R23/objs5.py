"""Apply my C21 rule (rows5.best) to every object in objects/*.txt; verify each object is an SDS first."""
import re, glob, sys, os, itertools
sys.argv = [sys.argv[0], os.getcwd()]
src = open('reviews/R23/rows5.py', encoding='utf-8').read().split('rows = list(')[0]
exec(src)
P = set(int(l.split('\t')[0][1:]) for l in open('scratch/settle-c21.tsv'))
for f in sorted(glob.glob('objects/O*.txt'), key=lambda s: int(re.findall(r'\d+', s)[0])):
    lines = [l.split() for l in open(f, encoding='utf-8').read().strip().splitlines()]
    head = ' '.join(lines[0])
    m = re.match(r'(\S+) \((\d+),\s*(\d+),\s*(-?\d+)\)', head)
    ms = [int(x) for x in re.findall(r'C(\d+)', m[1])]
    v, k, lam = int(m[2]), int(m[3]), int(m[4])
    D = {}
    for l in lines[1:]:
        coords = tuple(int(x) for x in l[:-1]); s = 1 if l[-1] == '+' else -1
        D[coords] = s
    ok = len(D) == k and all(len(c) == len(ms) for c in D)
    if ok and v <= 400:
        for g in itertools.product(*[range(m_) for m_ in ms]):
            if not any(g): continue
            t = 0
            for x, s in D.items():
                y = tuple((x[i] + g[i]) % ms[i] for i in range(len(ms)))
                t += s * D.get(y, 0)
            if t != lam: ok = False; break
    h = best(v, k, lam, ms)
    print(os.path.basename(f), head, 'sds' if ok else 'NOT-SDS/unchecked', 'RULE FIRES' if h else '-', h or '')
