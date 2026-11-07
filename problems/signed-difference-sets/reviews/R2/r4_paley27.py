"""Gordon Prop 2.3 (Paley and zero) in GF(27): P = nonzero squares, N = {0}; a (27,14,5) SDS in C3^3?
Also: is O9 affinely equivalent to it, and are the P parts of O9/O10 (N moved to 0) skew Hadamard DSs?"""
import itertools
from pathlib import Path
HERE = Path(__file__).resolve().parent
OBJ = HERE.parents[1] / "objects"
# GF(27) = GF(3)[x]/(x^3 - x - 1); element = coefficient tuple (c0, c1, c2)
def mul(a, b):
    r = [0] * 5
    for i in range(3):
        for j in range(3): r[i + j] += a[i] * b[j]
    for d in (4, 3):  # x^d = x^(d-2) + x^(d-3)
        c = r[d]; r[d] = 0; r[d - 2] += c; r[d - 3] += c
    return tuple(x % 3 for x in r[:3])
G3 = [tuple(t) for t in itertools.product(range(3), repeat=3)]
zero = (0, 0, 0)
sq = {mul(y, y) for y in G3 if y != zero}
D = {g: 1 for g in sq}; D[zero] = -1
def add(u, w, f): return tuple((s + t) % m for s, t, m in zip(u, w, f))
def counts(D, f, G):
    z = tuple(0 for _ in f)
    return sorted(set(sum(D[x] * D.get(add(x, g, f), 0) for x in D) for g in G if g != z))
print("Paley+zero GF(27): |P|", len(sq), "signed counts", counts(D, (3, 3, 3), G3))
def load(oid):
    out = {}
    for ln in (OBJ / (oid + ".txt")).read_text().split("\n")[1:]:
        if ln.strip():
            *c, s = ln.split(); out[tuple(map(int, c))] = 1 if s == "+" else -1
    return out
def det3(A):
    return (A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1]) - A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0]) + A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0])) % 3
def affine_equiv(D1, D2):
    for flat in itertools.product(range(3), repeat=9):
        A = [flat[0:3], flat[3:6], flat[6:9]]
        if det3(A) == 0: continue
        for t in G3:
            for sgn in (1, -1):
                img = {tuple((sum(A[i][j] * x[j] for j in range(3)) + t[i]) % 3 for i in range(3)): sgn * s for x, s in D1.items()}
                if img == D2: return (A, t, sgn)
    return None
o9 = load("O9")
print("O9 ~ Paley+zero (affine, +-):", affine_equiv(D, o9))
def p_part(Dobj, f):
    (n0,) = [x for x, s in Dobj.items() if s == -1]
    neg = tuple((-c) % m for c, m in zip(n0, f))
    return {add(x, neg, f) for x, s in Dobj.items() if s == 1}
def describe(P, f, G):
    z = tuple(0 for _ in f)
    negP = {tuple((-c) % m for c, m in zip(x, f)) for x in P}
    skew = not (P & negP) and len(P | negP) == len(G) - 1
    lam = sorted(set(sum(1 for x in P if add(x, g, f) in P) for g in G if g != z))
    return "skew=%s, DS intersection numbers=%s" % (skew, lam)
print("O9 P-part:", describe(p_part(o9, (3, 3, 3)), (3, 3, 3), G3))
G39 = [(a, b) for a in range(3) for b in range(9)]
print("O10 P-part:", describe(p_part(load("O10"), (3, 9)), (3, 9), G39))
