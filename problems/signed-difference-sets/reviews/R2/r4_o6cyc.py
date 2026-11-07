"""Is O6 affinely equivalent (GL(2,5) + translation, +-) to an eighth-power cyclotomic SDS in F_25?"""
import itertools
from pathlib import Path
OBJ = Path(__file__).resolve().parents[2] / "objects"
o6 = {}
for ln in (OBJ / "O6.txt").read_text().split("\n")[1:]:
    if ln.strip():
        *c, s = ln.split(); o6[tuple(map(int, c))] = 1 if s == "+" else -1
def mul(a, b): return ((a[0] * b[0] + 2 * a[1] * b[1]) % 5, (a[0] * b[1] + a[1] * b[0]) % 5)
els = [(a, b) for a in range(5) for b in range(5)]
def ordr(x):
    y = x; o = 1
    while y != (1, 0): y = mul(y, x); o += 1
    return o
g = next(x for x in els if x != (0, 0) and ordr(x) == 24)
pw = [(1, 0)]
for _ in range(23): pw.append(mul(pw[-1], g))
cls = [[pw[i] for i in range(j, 24, 8)] for j in range(8)]
add = lambda u, w: ((u[0] + w[0]) % 5, (u[1] + w[1]) % 5)
cands = []
for chosen in itertools.combinations(range(8), 4):
    for signs in itertools.product((1, -1), repeat=4):
        D = {x: s for c, s in zip(chosen, signs) for x in cls[c]}
        if all(sum(D[x] * D.get(add(x, h), 0) for x in D) == 1 for h in els if h != (0, 0)):
            cands.append(D)
def equiv(D1, D2):
    for a, b, c, d in itertools.product(range(5), repeat=4):
        if (a * d - b * c) % 5 == 0: continue
        for t in els:
            for sgn in (1, -1):
                img = {((a * x + b * y + t[0]) % 5, (c * x + d * y + t[1]) % 5): sgn * s for (x, y), s in D1.items()}
                if img == D2: return ((a, b), (c, d)), t, sgn
    return None
res = [equiv(D, o6) for D in cands]
print(len(cands), "cyclotomic sets; O6 equivalent to one:", next((r for r in res if r), None))
