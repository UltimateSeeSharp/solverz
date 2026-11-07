"""Structure of O6 (C5^2), O8, O10 (C3xC9): stabilizer in Aut(G) x translations (up to global sign),
and for C5^2: does F_25 have an SDS (25,12,1) that is a union of eighth-power cyclotomic classes
(size 3), possibly with 0, and is O6 equivalent to one?"""
import itertools
from pathlib import Path
OBJ = Path(__file__).resolve().parents[2] / "objects"
def load(oid):
    out = {}
    for ln in (OBJ / (oid + ".txt")).read_text().split("\n")[1:]:
        if ln.strip():
            *c, s = ln.split(); out[tuple(map(int, c))] = 1 if s == "+" else -1
    return out
def autos(f):
    """All automorphisms of prod Z_f as images of the standard generators."""
    G = list(itertools.product(*[range(m) for m in f]))
    def order(x):
        o = 1; y = x
        while any(y):
            y = tuple((a + b) % m for a, b, m in zip(y, x, f)); o += 1
        return o
    res = []
    for ims in itertools.product(G, repeat=len(f)):
        if any(order(im) != m and (m % order(im) != 0) for im, m in zip(ims, f)): continue
        if any(m % order(im) for im, m in zip(ims, f)): continue
        def phi(x, ims=ims):
            return tuple(sum(c * im[i] for c, im in zip(x, ims)) % f[i] for i in range(len(f)))
        img = {phi(x) for x in G}
        if len(img) == len(G): res.append(phi)
    return G, res
def stabilizer(D, f):
    G, A = autos(f)
    n = 0
    for phi in A:
        for t in G:
            for sgn in (1, -1):
                img = {tuple((a + b) % m for a, b, m in zip(phi(x), t, f)): sgn * s for x, s in D.items()}
                if img == D: n += 1
    return len(A), n
for oid, f in (("O6", (5, 5)), ("O8", (3, 9)), ("O10", (3, 9))):
    na, ns = stabilizer(load(oid), f)
    print(oid, f, "|Aut|", na, "| stabilizer in Aut x G x {+-1}:", ns)
# F_25 = F_5[w]/(w^2 - 2) (2 is a nonsquare mod 5); find a primitive element
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
def is_sds(D, k, lam):
    return len(D) == k and all(sum(D[x] * D.get(add(x, h), 0) for x in D) == lam for h in els if h != (0, 0))
hits = []
for r in range(1, 9):
    for chosen in itertools.combinations(range(8), r):
        for signs in itertools.product((1, -1), repeat=r):
            for z in (0, 1, -1):
                D = {}
                for c, s in zip(chosen, signs):
                    for x in cls[c]: D[x] = s
                if z: D[(0, 0)] = z
                if len(D) == 12 and is_sds(D, 12, 1): hits.append((chosen, signs, z))
print("eighth-power cyclotomic (25,12,1) SDSs in F_25 (classes, signs, zero):", len(hits), hits[:4])
