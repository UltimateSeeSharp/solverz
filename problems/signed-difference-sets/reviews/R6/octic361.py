"""Rebuild O12's described structure independently: GF(361) = F19[x]/(x^2-2) (2 is a non-residue mod 19),
octic classes C_j = g^j <g^8>; D = -(C0..C5 + {0}) + C7 (zero on C6). Check IsSDS on (F19^2,+) = C19 x C19,
for every labelling a in {1,3,5,7} (g -> g^a); also check O12 is constant on the octic classes up to an
automorphism (test: is supp/sign pattern of O12 a union of classes for the identity coordinate map)."""
import sys
sys.path.insert(0, "problems/signed-difference-sets/reviews/R6")
from verify import check
p, r = 19, 2
def mul(a, b): return ((a[0]*b[0] + r*a[1]*b[1]) % p, (a[0]*b[1] + a[1]*b[0]) % p)
def pw(a, e):
    res = (1, 0)
    while e:
        if e & 1: res = mul(res, a)
        a = mul(a, a); e >>= 1
    return res
def order(a):
    x, n = a, 1
    while x != (1, 0): x = mul(x, a); n += 1
    return n
g = next((x, y) for x in range(p) for y in range(1, p) if order((x, y)) == 360)
for a in (1, 3, 5, 7):
    ga = pw(g, a)
    cls = {}
    x = (1, 0)
    for i in range(360):
        cls[x] = i % 8; x = mul(x, ga)
    ent = [((0, 0), -1)] + [(e, -1 if j <= 5 else 1) for e, j in cls.items() if j != 6]
    print("g=", g, "a=", a, check("SDS(361,316,141,[19,19])", ent))
