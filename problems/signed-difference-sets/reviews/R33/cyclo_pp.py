# Signed unions of cyclotomic classes (order e) and {0} in GF(p^m), m >= 2, q < 500, on C_p^m: open rows settled?
import csv, re, sys, itertools, numpy as np
rows = list(csv.DictReader(open(sys.argv[1] + '/instances.csv', encoding='utf-8')))
st = {}
for r in rows:
    m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", r['key'])
    sh = tuple(int(x) for x in m.group(4).split(','))
    if len(set(sh)) == 1 and len(sh) > 1: st[tuple(int(x) for x in m.groups()[:3])] = (r['id'], r['status'], r['solution'])
def polymulmod(a, b, f, p):  # coefficient lists, low first; f monic of degree m
    m = len(f) - 1; r = [0] * (2 * m - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i + j] = (r[i + j] + x * y) % p
    for d in range(len(r) - 1, m - 1, -1):
        c = r[d]
        if c:
            for i in range(m + 1): r[d - m + i] = (r[d - m + i] - c * f[i]) % p
    return r[:m]
hits = {}
for p, m in [(3, 2), (5, 2), (3, 3), (7, 2), (3, 4), (11, 2), (5, 3), (13, 2), (3, 5), (17, 2), (7, 3), (19, 2)]:
    q = p ** m
    for f in itertools.product(range(p), repeat=m):  # find f = x^m + ... with x primitive
        f = list(f) + [1]; x = [0, 1] + [0] * (m - 2); e1 = [1] + [0] * (m - 1); cur = e1[:]; seen = set()
        for i in range(q - 1):
            seen.add(tuple(cur)); cur = polymulmod(cur, x, f, p)
        if len(seen) == q - 1 and cur == e1: break
    lg = {}; cur = e1[:]
    for i in range(q - 1): lg[tuple(cur)] = i; cur = polymulmod(cur, x, f, p)
    for e in [d for d in (2, 3, 4, 6, 8) if (q - 1) % d == 0]:
        cls = [np.zeros((p,) * m) for _ in range(e)]
        for v, i in lg.items(): cls[i % e][v] = 1
        z = np.zeros((p,) * m); z[(0,) * m] = 1
        for signs in itertools.product((-1, 0, 1), repeat=e + 1):
            if all(s == 0 for s in signs[:e]): continue
            D = sum(s * c for s, c in zip(signs, cls + [z]))
            F = np.fft.fftn(D); ac = np.rint(np.fft.ifftn(F * np.conj(F)).real).astype(int).ravel()
            if len(set(ac[1:])) == 1:
                t = (q, int(ac[0]), int(ac[1]))
                if t in st: hits.setdefault(t, (st[t], e, signs))
for t, x in sorted(hits.items()): print(t, x)
