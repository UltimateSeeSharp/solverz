# Signed unions of cyclotomic classes (order e) and {0} in Z_p, p prime < 500: which open rows do they settle?
import csv, re, sys, itertools, numpy as np
rows = list(csv.DictReader(open(sys.argv[1] + '/instances.csv', encoding='utf-8')))
st = {}
for r in rows:
    m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[(\d+)\]\)", r['key'])
    if m: st[tuple(int(x) for x in m.groups()[:3])] = (r['id'], r['status'], r['solution'], r['id'] in sys.argv[2].split(','))
def primroot(p):
    fac = [q for q in range(2, p) if (p - 1) % q == 0 and all(q % d for d in range(2, q))]
    return next(g for g in range(2, p) if all(pow(g, (p - 1) // q, p) != 1 for q in fac))
hits = {}
for p in [x for x in (211, 421, 29, 61, 349) if all(x % d for d in range(2, int(x**.5) + 1))]:
    g = primroot(p); lg = {pow(g, i, p): i for i in range(p - 1)}
    for e in (2, 4, 6, 8):
        if (p - 1) % e: continue
        cls = [np.zeros(p) for _ in range(e)]
        for x in range(1, p): cls[lg[x] % e][x] = 1
        z = np.zeros(p); z[0] = 1
        parts = cls + [z]
        for signs in itertools.product((-1, 0, 1), repeat=e + 1):
            if signs[0] == 0 and all(s == 0 for s in signs[:e]): continue
            D = sum(s * c for s, c in zip(signs, parts))
            F = np.fft.fft(D); ac = np.rint(np.fft.ifft(F * np.conj(F)).real).astype(int)
            if len(set(ac[1:])) == 1:
                t = (p, int(ac[0]), int(ac[1]))
                if t in st and st[t][1] in ('open','exists'): hits.setdefault(t, (st[t], e, signs))
for t, x in sorted(hits.items()): print(t, x)
print('done')
