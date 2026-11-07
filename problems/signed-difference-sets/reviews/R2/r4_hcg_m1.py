"""He-Chen-Ge (arXiv 2306.05631) Sec 4 product construction at m = 1 (their Thm 4.1 states m even):
G = G0 x G1 x G1 = C3^3, D' = {1} - {2} (a (3,2,-1) SDS in C3, Gordon Prop 2.2 with v = 3),
D = (x0, 0, G1) + (0, G1, x1) + (0, D', D'). Is it a (27,10,1) SDS, and is O7 equivalent to it?"""
import itertools
from pathlib import Path
OBJ = Path(__file__).resolve().parents[2] / "objects"
G3 = [tuple(t) for t in itertools.product(range(3), repeat=3)]
add = lambda u, w: tuple((s + t) % 3 for s, t in zip(u, w))
def counts(D):
    return sorted(set(sum(D[x] * D.get(add(x, g), 0) for x in D) for g in G3 if g != (0, 0, 0)))
Dp = {1: 1, 2: -1}
def build(x0, x1):
    D = {}
    def put(e, s):
        D[e] = D.get(e, 0) + s
    for y in range(3): put((x0, 0, y), 1)
    for y in range(3): put((0, y, x1), 1)
    for a, sa in Dp.items():
        for b, sb in Dp.items(): put((0, a, b), sa * sb)
    return {e: s for e, s in D.items() if s != 0}, max(abs(s) for s in D.values())
for x0 in (1, 2):
    for x1 in range(3):
        D, mx = build(x0, x1)
        print("x0=%d x1=%d: support %d, max |coef| %d, ternary %s, signed counts %s" % (x0, x1, len(D), mx, mx <= 1, counts(D)))
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
D, _ = build(1, 0)
print("O7 ~ HCG m=1 (x0=1,x1=0):", affine_equiv(D, load("O7")))
