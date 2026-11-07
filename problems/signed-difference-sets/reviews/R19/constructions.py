# Classical difference sets with 3-rank >= 2 (and their complements and +-1 versions G - 2D): C20 must stay silent.
import itertools, math
from eis_lib import is_sds, eis_check
def gf(p, poly):  # GF(p^d) as tuples, poly: monic coefficients c0..c_{d-1} of x^d = -(c0 + ... ) ; returns elements, mul
    d = len(poly)
    els = list(itertools.product(range(p), repeat=d))
    def mul(a, b):
        r = [0] * (2 * d - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b): r[i + j] = (r[i + j] + x * y) % p
        for e in range(2 * d - 2, d - 1, -1):
            c = r[e]; r[e] = 0
            for i, ci in enumerate(poly): r[e - d + i] = (r[e - d + i] - c * ci) % p
        return tuple(r[:d])
    return els, mul
def squares(els, mul):
    z = tuple(0 for _ in els[0]); return {mul(x, x) for x in els if x != z}
GF9 = gf(3, [1, 0])        # x^2 = -1
GF27 = gf(3, [-1 % 3, -1 % 3, 0])  # x^3 = x + 1
GF25 = gf(5, [-2 % 5, 0])  # x^2 = 2 (2 non-square mod 5)
def prime_field(p): return [(x,) for x in range(p)], (lambda a, b: ((a[0] * b[0]) % p,))
def twin(F1, F2):
    (e1, m1), (e2, m2) = F1, F2; s1, s2 = squares(e1, m1), squares(e2, m2)
    z1, z2 = e1[0], e2[0]
    D = {}
    for x in e1:
        for y in e2:
            if x != z1 and y != z2 and ((x in s1) == (y in s2)): D[x + y] = 1
            if y == z2: D[x + y] = 1
    return D
def hyperplanes(d):  # hyperplanes of GF(3)^d through 0
    hs = set()
    for c in itertools.product(range(3), repeat=d):
        if any(c) and next(x for x in c if x) == 1:
            hs.add(frozenset(x for x in itertools.product(range(3), repeat=d) if sum(a * b for a, b in zip(c, x)) % 3 == 0))
    return sorted(hs, key=sorted)
def mcfarland(d, K):  # E = GF(3)^(d+1), K elements list (tuples); uses |hyperplanes| of the K elements
    H = hyperplanes(d + 1); D = {}
    for h, g in zip(H, K): 
        for x in h: D[x + g] = 1
    return D
def spence(d, K):
    H = hyperplanes(d + 1); E = list(itertools.product(range(3), repeat=d + 1)); D = {}
    for i, (h, g) in enumerate(zip(H, K)):
        for x in (set(E) - h if i == 0 else h): D[x + g] = 1
    assert len(H) == len(K)
    return D
def cyc(n): return [(i,) for i in range(n)]
def prod(*gs): return [sum(t, ()) for t in itertools.product(*gs)]
cases = []
e27, m27 = GF27; cases.append(("Paley GF(27)", [3, 3, 3], {x: 1 for x in squares(e27, m27)}))
cases.append(("twin 9,11", [3, 3, 11], twin(GF9, prime_field(11))))
cases.append(("twin 25,27", [5, 5, 3, 3, 3], twin(GF25, GF27)))
cases.append(("twin 27,29", [3, 3, 3, 29], twin(GF27, prime_field(29))))
cases.append(("McFarland q=3 d=1, C5", [3, 3, 5], mcfarland(1, cyc(5))))
cases.append(("McFarland q=3 d=2, C14", [3, 3, 3, 14], mcfarland(2, cyc(14))))
cases.append(("McFarland q=3 d=2, C2xC7", [3, 3, 3, 2, 7], mcfarland(2, prod(cyc(2), cyc(7)))))
cases.append(("Spence d=1, C4", [3, 3, 4], spence(1, cyc(4))))
cases.append(("Spence d=1, C2xC2", [3, 3, 2, 2], spence(1, prod(cyc(2), cyc(2)))))
cases.append(("Spence d=2, C13", [3, 3, 3, 13], spence(2, cyc(13))))
sp = spence(1, prod(cyc(2), cyc(2)))  # Menon product with {0} in C2^2: (144,66,30)
G1 = prod(cyc(2), cyc(2)); G2 = list(itertools.product(range(3), range(3), range(2), range(2)))
cases.append(("Menon (4,1,0)x(36,15,6)", [2, 2, 3, 3, 2, 2],
              {g1 + g2: 1 for g1 in G1 for g2 in G2 if (g1 == (0, 0)) != (g2 in sp)}))
def params(ms, D):
    v = math.prod(ms); k = len(D); lam = (k * k - k) // (v - 1) if all(x == 1 for x in D.values()) else None
    return v, k, lam
for name, ms, D in cases:
    v, k, lam = params(ms, D)
    G = list(itertools.product(*[range(m) for m in ms]))
    comp = {g: 1 for g in G if g not in D}
    pm = {g: (-1 if g in D else 1) for g in G}
    n = k - lam
    for tag, E, kk, ll in (("D", D, k, lam), ("G-D", comp, v - k, v - 2 * k + lam), ("G-2D", pm, v, v - 4 * n),
                           ("-D", {g: -1 for g in D}, k, lam)):
        ok = is_sds(ms, E, ll)
        viol, fired, r = eis_check(ms, E, kk, ll)
        print(f"{name:28s} {tag:5s} {ms} ({v},{kk},{ll}) sds={ok} 3-rank={r} viol={len(viol)} {viol[:2]} fired={fired}", flush=True)
