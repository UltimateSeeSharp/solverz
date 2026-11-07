"""Gordon arXiv:2212.10630 Thm 4.1 for q=3, r=9: (27,17,8) SDS in (GF(3),+) + (GF(9),+) = C3^3."""
import itertools
# GF(9) = GF(3)[i]/(i^2+1); element (a,b) = a + b i
def mul9(x, y):
    a, b = x; c, d = y
    return ((a * c - b * d) % 3, (a * d + b * c) % 3)
def pow9(x, e):
    r = (1, 0)
    for _ in range(e): r = mul9(r, x)
    return r
def chi3(x): return 0 if x == 0 else (1 if x == 1 else -1)
def chi9(y):
    if y == (0, 0): return 0
    return 1 if pow9(y, 4) == (1, 0) else -1
G = [(x, a, b) for x in range(3) for a in range(3) for b in range(3)]
P = [(x, a, b) for (x, a, b) in G if chi3(x) * chi9((a, b)) == 1] + [(0, a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]
N = [(0, 0, 0)]
D = {g: 1 for g in P}; D.update({g: -1 for g in N})
add = lambda u, w: tuple((s + t) % 3 for s, t in zip(u, w))
counts = sorted(set(sum(D[x] * D.get(add(x, g), 0) for x in D) for g in G if g != (0, 0, 0)))
print("|P|", len(P), "|N|", len(N), "k", len(D), "signed counts over g != 0:", counts)
# equivalence test with O11: is O11 an image of this set under an affine automorphism x -> Ax + t (A in GL(3,3))?
o11 = {}
for ln in open(__file__.replace("r4_gordon41.py", "../../objects/O11.txt")).read().split("\n")[1:]:
    if ln.strip():
        *c, s = ln.split(); o11[tuple(map(int, c))] = 1 if s == "+" else -1
def apply(A, t, x):
    return tuple((sum(A[i][j] * x[j] for j in range(3)) + t[i]) % 3 for i in range(3))
def det3(A):
    return (A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1]) - A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0]) + A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0])) % 3
found = None
for flat in itertools.product(range(3), repeat=9):
    A = [flat[0:3], flat[3:6], flat[6:9]]
    if det3(A) == 0: continue
    for t in G:
        for sgn in (1, -1):
            img = {apply(A, t, x): sgn * s for x, s in D.items()}
            if img == o11: found = (A, t, sgn); break
        if found: break
    if found: break
print("O11 equivalent to Gordon Thm 4.1 set:", found)
