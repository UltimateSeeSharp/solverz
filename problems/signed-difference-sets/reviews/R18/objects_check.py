# Objects O1-O39: verify SDS, Gaussian character identities on G/4G, and that C19 never fires (N <= 256).
import math, re, itertools
from kill import PF, kills
def load(i):
    L = open(PF / f"objects/O{i}.txt", encoding="utf-8").read().split("\n")
    m = re.match(r"(\S+) \((\d+),(\d+),(-?\d+)\)", L[0])
    ms = [int(x) for x in m.group(1).replace("C", "").split("x")]
    v, k, lam = int(m.group(2)), int(m.group(3)), int(m.group(4))
    D = {}
    for l in L[1:]:
        p = l.split()
        if not p: continue
        D[tuple(int(x) for x in p[:-1])] = 1 if p[-1] == "+" else -1
    return ms, v, k, lam, D
res = []
for i in range(1, 40):
    ms, v, k, lam, D = load(i)
    assert math.prod(ms) == v and len(D) == k
    pts = list(D.items())
    # SDS check (skip the 4096 one: too slow in python; checked by characters below only)
    if v <= 500:
        ok = all(sum(d * D.get(tuple((a + b) % mm for a, b, mm in zip(x, g, ms)), 0) for x, d in pts) == lam
                 for g in itertools.product(*[range(mm) for mm in ms]) if any(g))
    else: ok = None
    e = [1 if mm % 4 == 0 else 2 if mm % 2 == 0 else 0 for mm in ms]
    rng = [4 if ei == 1 else 2 if ei == 2 else 1 for ei in e]
    N = math.prod(rng); n = k - lam; viol = 0; tot = 0
    m = math.isqrt(n) if n >= 0 else -1
    a0 = sum(d for x, d in pts if all(r == 1 or xi % r == 0 for xi, r in zip(x, rng)))
    vals = {}
    for c in itertools.product(*[range(r) for r in rng]):
        A = B = 0
        for x, d in pts:
            t = sum(ei * ci * xi for ei, ci, xi in zip(e, c, x)) % 4
            if t == 0: A += d
            elif t == 1: B += d
            elif t == 2: A -= d
            else: B -= d
        vals[c] = (A, B); tot += A
        real = all((ei * ci * 2) % 4 == 0 for ei, ci in zip(e, c))
        if any(c) and A * A + B * B != n: viol += 1
        if any(c) and real and (B != 0 or abs(A) != m or m * m != n): viol += 1
    for c, (A, B) in vals.items():
        nc = tuple((r - ci) % r for r, ci in zip(rng, c))
        if vals[nc] != (A, -B): viol += 1
    if tot != N * a0: viol += 1
    fired = []
    S = k + lam * (v - 1); s = math.isqrt(S)
    if N > 1 and m * m == n and s * s == S:
        c4 = sum(1 for x in ms if x % 4 == 0); c2 = sum(1 for x in ms if x % 2 == 0)
        for a in range(0, c4 + 1):
            for b in range(0, c2 - a + 1):
                NN = 4 ** a * 2 ** b
                if 1 < NN <= 256 and kills(NN, m, s): fired.append(NN)
    print(f"O{i} {ms} ({v},{k},{lam}) sds={ok} |G/4G|={N} viol={viol} fired={fired}")
