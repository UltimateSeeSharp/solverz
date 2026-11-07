# Own GF(361) cyclotomy: rebuild the order-8 construction and compare to O12 under GL(2,19).
import itertools, numpy as np
p = 19; NR = 2  # 2 is a non-square mod 19, so GF(361) = GF(19)[x]/(x^2 - 2)
def mul(a, b):  # (a0 + a1 x)(b0 + b1 x)
    return ((a[0]*b[0] + NR*a[1]*b[1]) % p, (a[0]*b[1] + a[1]*b[0]) % p)
def pw(a, e):
    r = (1, 0)
    while e:
        if e & 1: r = mul(r, a)
        a = mul(a, a); e >>= 1
    return r
q = p*p
def is_prim(g):
    return all(pw(g, (q-1)//r) != (1, 0) for r in (2, 3, 5))
gen = next((a, b) for a in range(p) for b in range(1, p) if is_prim((a, b)))
logs = {}
x = (1, 0)
for e in range(q-1):
    logs[x] = e; x = mul(x, gen)
assert len(logs) == q-1
cls = lambda z: logs[z] % 8
def is_sds(D):
    pts = list(D.items()); vals = set()
    for g in itertools.product(range(p), repeat=2):
        if g == (0, 0): continue
        s = sum(d * D.get(((a+g[0]) % p, (b+g[1]) % p), 0) for (a, b), d in pts)
        vals.add(s)
    return vals
# sign shape "------0+|-": C0..C5 -, C6 0, C7 +, zero -
shape = {0: -1, 1: -1, 2: -1, 3: -1, 4: -1, 5: -1, 6: 0, 7: 1}
D = {(0, 0): -1}
for z in logs:
    if shape[cls(z)]: D[z] = shape[cls(z)]
print("generator", gen, "|D|", len(D), "signed counts", is_sds(D))
# every shape with weights on two classes i,j: -(G - Ci - Cj) [0 marked -] + Cj, list which (i,j) work
hits = []
for i in range(8):
    for j in range(8):
        if i == j: continue
        E = {(0, 0): -1}
        for z in logs:
            c = cls(z)
            if c == j: E[z] = 1
            elif c != i: E[z] = -1
        v = is_sds(E)
        if len(v) == 1: hits.append((i, j, v))
print("(zero class i, plus class j) hits:", hits)
# Compare to O12 under linear maps (a,b) -> A (a,b), and sign +-1
base = "problems/signed-difference-sets/"
O = {}
for ln in open(base + "objects/O12.txt").read().split("\n")[1:]:
    if ln.strip():
        a, b, s = ln.split(); O[(int(a), int(b))] = 1 if s == "+" else -1
Ogrid = np.zeros((p, p), dtype=np.int8)
for (a, b), s in O.items(): Ogrid[a, b] = s
Dpts = np.array(list(D.keys())); Dval = np.array([D[tuple(t)] for t in Dpts], dtype=np.int8)
found = []
for a, b, c, d in itertools.product(range(p), repeat=4):
    if (a*d - b*c) % p == 0: continue
    X = (a*Dpts[:, 0] + b*Dpts[:, 1]) % p; Y = (c*Dpts[:, 0] + d*Dpts[:, 1]) % p
    img = Ogrid[X, Y]
    for sg in (1, -1):
        if np.all(img == sg*Dval):
            found.append(((a, b, c, d), sg))
print("linear maps GF(361)-coords -> O12 (count):", len(found), found[:3])
# Compare each hit (zero class i, plus class j) to O12 under GL(2,19) and sign.
mats = [(a, b, c, d) for a, b, c, d in itertools.product(range(p), repeat=4) if (a*d - b*c) % p]
tot = 0
for (i, j, _) in hits:
    E = {(0, 0): -1}
    for z in logs:
        c = cls(z)
        if c == j: E[z] = 1
        elif c != i: E[z] = -1
    Ep = np.array(list(E.keys())); Ev = np.array([E[tuple(t)] for t in Ep], dtype=np.int8)
    n = 0
    for a, b, c, d in mats:
        X = (a*Ep[:, 0] + b*Ep[:, 1]) % p; Y = (c*Ep[:, 0] + d*Ep[:, 1]) % p
        img = Ogrid[X, Y]
        if np.all(img == -Ev): n += 1
    print("hit", (i, j), "linear maps onto -O12:", n); tot += n
print("total", tot)
