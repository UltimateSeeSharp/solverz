"""C28 on every object with 4 | n: for quotients Z_(2r) x Z_d (r a power of 2, d odd with d | 2^i+1) by random surjective
forms, check Ma's step Y(h+u) = Y(h) mod 2, W even, and Z = W/2 meets every demand of C28."""
import sys, re, glob, itertools, random, math
from math import gcd, prod, lcm, isqrt
from functools import reduce
random.seed(2)
root = sys.argv[1]
st = dict(objs=0, quot=0, fail=0)
def selfconj(d):
    return any((2 ** i + 1) % d == 0 for i in range(1, 2 * d + 2))
for path in sorted(glob.glob(root + "/objects/O*.txt")):
    lines = open(path, encoding="utf-8").read().split("\n")
    hdr = re.match(r"(\S+) \((\d+),(\d+),(-?\d+)\)", lines[0])
    ms = [int(x) for x in hdr.group(1).replace("C", "").split("x")]
    v, k, lam = int(hdr.group(2)), int(hdr.group(3)), int(hdr.group(4))
    n = k - lam
    if n % 4: continue
    D = {}
    for ln in lines[1:]:
        if ln.strip():
            *xs, s = ln.split(); D[tuple(map(int, xs))] = 1 if s == "+" else -1
    st["objs"] += 1
    s = sum(D.values())
    assert s * s == k + lam * (v - 1), path
    w = reduce(lcm, ms)
    for r in [1, 2, 4, 8, 16, 32, 64, 128]:
        for d in range(1, w + 1, 2):
            if w % (2 * r) or w % d or not selfconj(d): continue
            m1, m2 = 2 * r, d
            if v % (m1 * m2): continue
            # need a surjection G -> Z_m1 x Z_m2; try random forms
            forms = set()
            for _ in range(40):
                A1 = tuple(random.randrange(0, m1, m1 // gcd(m1, q)) for q in ms)
                A2 = tuple(random.randrange(0, m2, m2 // gcd(m2, q)) for q in ms)
                img = {(sum(a * x for a, x in zip(A1, e)) % m1, sum(a * x for a, x in zip(A2, e)) % m2)
                       for e in itertools.product(*[range(min(q, m1 * m2)) for q in ms])}
                if len(img) == m1 * m2: forms.add((A1, A2))
                if len(forms) >= 3: break
            for A1, A2 in forms:
                st["quot"] += 1
                c = v // (m1 * m2)
                Y = {}
                for x, sg in D.items():
                    h = (sum(a * xi for a, xi in zip(A1, x)) % m1, sum(a * xi for a, xi in zip(A2, x)) % m2)
                    Y[h] = Y.get(h, 0) + sg
                Yf = lambda a, b: Y.get((a % m1, b % m2), 0)
                ok = all((Yf(a + r, b) - Yf(a, b)) % 2 == 0 for a in range(m1) for b in range(m2))
                W = {(a, b): Yf(a, b) + Yf(a + r, b) for a in range(r) for b in range(m2)}
                ok &= all(x % 2 == 0 for x in W.values())
                Z = {h: x // 2 for h, x in W.items()}
                Q = sum(z * z for z in Z.values())
                ok &= 4 * Q == k + lam * (2 * c - 1)
                for g in Z:
                    if g == (0, 0): continue
                    ok &= 2 * sum(Z[h] * Z[((h[0] + g[0]) % r, (h[1] + g[1]) % m2)] for h in Z) == lam * c
                ok &= sum(Z.values()) in (s // 2, -s // 2) and all(abs(z) <= c for z in Z.values())
                sa = sum(abs(z) for z in Z.values())
                ok &= 2 * sa <= k and (sa - s // 2) % 2 == 0
                if not ok:
                    st["fail"] += 1; print("FAIL", path, r, d, A1, A2)
print(st)
