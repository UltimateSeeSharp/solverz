"""C9/C10 on the known objects O*.txt: SDS check, then (if n squarefree, gcd(v,n)=1) a translate
fixed by all of T; C10 on every coordinatewise quotient prod Z_{d_i} (d_i | m_i) with gcd(|H|,n)=1."""
import sys, math, itertools, glob, os, re
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from brute import G, T_set, sqfree, fixed_translate, all_units

def load(path):
    lines = open(path).read().split('\n')
    m = re.match(r'\s*(\S+)\s*\((\d+),(-?\d+),(-?\d+)\)', lines[0])
    shape = [int(x) for x in re.findall(r'\d+', m[1].replace('\u00d7', 'x'))]
    v, k, lam = int(m[2]), int(m[3]), int(m[4])
    pts = []
    for l in lines[1:]:
        p = l.split()
        if not p: continue
        pts.append((tuple(int(x) for x in p[:-1]), 1 if p[-1] == '+' else -1))
    return shape, v, k, lam, pts

def main():
    base = sys.argv[1]
    for path in sorted(glob.glob(os.path.join(base, 'O*.txt')), key=lambda s: int(re.findall(r'O(\d+)', s)[0])):
        name = os.path.basename(path)
        shape, v, k, lam, pts = load(path)
        if math.prod(shape) != v or v > 4000:
            print(name, 'skip', shape, v); continue
        g = G(shape)
        a = np.zeros(v, np.int64)
        for x, s in pts: a[g.idx[x]] = s
        ac = np.array([(a * a[g.add[:, s]]).sum() for s in range(v)])
        ok = ac[0] == k and all(ac[1:] == lam) and len(pts) == k
        n = k - lam
        res = f'{name} {shape} ({v},{k},{lam}) n={n} sds={ok}'
        if math.gcd(v, n) == 1 and sqfree(n):
            T = T_set(g, n)
            c = fixed_translate(g, a, T)
            res += f' C9: |T|={len(T)} translate={c}'
            if c is None: res += ' COUNTEREXAMPLE'
        else:
            res += f' C9 n/a (gcd={math.gcd(v, n)}, sqf={sqfree(n)})'
        # C10 on coordinatewise quotients
        tested = fails = 0
        for ds in itertools.product(*[[d for d in range(1, m + 1) if m % d == 0] for m in shape]):
            hv = math.prod(ds)
            if hv == v or hv == 1 or math.gcd(hv, n) != 1 or not sqfree(n): continue
            hshape = [d for d in ds if d > 1]
            h = G(hshape)
            b = np.zeros(h.v, np.int64)
            for x, s in pts:
                y = tuple(xi % d for xi, d in zip(x, ds) if d > 1)
                b[h.idx[y]] += s
            c = v // hv
            acb = np.array([(b * b[h.add[:, s]]).sum() for s in range(h.v)])
            assert acb[0] == n + lam * c and all(acb[1:] == lam * c), (name, ds)
            tested += 1
            if fixed_translate(h, b, T_set(h, n)) is None:
                fails += 1; print('C10 COUNTEREXAMPLE', name, ds, b.tolist())
        res += f' C10 quotients tested={tested} fails={fails}'
        print(res, flush=True)

main()
