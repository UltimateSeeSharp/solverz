"""Independent recheck of O34-O38: direct autocorrelation, group-ring product, Lean masks."""
import re, sys, cmath
PF = "problems/signed-difference-sets"
OBJ = {"O34": "N1164", "O35": "N3486", "O36": "N11650", "O37": "N11991", "O38": "N58470"}

def load(o):
    lines = open(f"{PF}/objects/{o}.txt").read().split("\n")
    m = re.match(r"C(\d+) \((\d+),(\d+),(-?\d+)\)", lines[0])
    n, v, k, lam = map(int, m.groups())
    assert n == v
    D = [0] * v
    seen = set()
    for ln in lines[1:]:
        if not ln.strip():
            continue
        x, s = ln.split()
        x = int(x)
        assert 0 <= x < v and x not in seen, (o, x)
        seen.add(x)
        D[x] = {"+": 1, "-": -1}[s]
    return v, k, lam, D

def direct(v, D):
    return [sum(D[x] * D[(x + g) % v] for x in range(v)) for g in range(v)]

def groupring(v, D):
    # D * D^(-1) as polynomial product mod x^v - 1: coefficient at g = sum_{a-b=g} D(a)D(b)
    c = [0] * v
    for a in range(v):
        if D[a]:
            for b in range(v):
                if D[b]:
                    c[(a - b) % v] += D[a] * D[b]
    return c

def dft_ok(v, k, lam, D):
    s = sum(D)
    ok = s * s == k + lam * (v - 1)
    worst = 0.0
    for j in range(1, v):
        z = sum(D[x] * cmath.exp(2j * cmath.pi * j * x / v) for x in range(v))
        worst = max(worst, abs(abs(z) ** 2 - (k - lam)))
    return ok, worst, s

def lean_masks(n):
    t = open(f"{PF}/lean/SignedDifferenceSets/Answer/{n}.lean", encoding="utf-8").read()
    P = int(re.search(r"def plus : ℕ := (0x[0-9a-f]+)", t).group(1), 16)
    N = int(re.search(r"def minus : ℕ := (0x[0-9a-f]+)", t).group(1), 16)
    st = re.search(r"HasSDS \(ZMod (\d+)\) (\d+) (-?\d+)", t).groups()
    st2 = re.search(r"IsSDS (\d+) (-?\d+) sds", t).groups()
    return P, N, tuple(map(int, st)), tuple(map(int, st2))

for o, n in OBJ.items():
    v, k, lam, D = load(o)
    supp = sum(1 for d in D if d)
    a = direct(v, D)
    b = groupring(v, D)
    ok_dir = all(a[g] == lam for g in range(1, v)) and a[0] == supp == k
    ok_gr = all(b[g] == lam for g in range(1, v)) and b[0] == k
    ok_dft, worst, s = dft_ok(v, k, lam, D)
    P, N, st, st2 = lean_masks(n)
    Dl = [1 if (P >> i) & 1 else (-1 if (N >> i) & 1 else 0) for i in range(v)]
    extra = (P >> v) | (N >> v)
    print(o, n, (v, k, lam), "supp", supp, "plus", D.count(1), "minus", D.count(-1), "sum", s,
          "direct", ok_dir, "groupring", ok_gr, "dft", ok_dft, f"{worst:.1e}",
          "lean_stmt", st, st2, "lean==obj", Dl == D, "P&N", P & N, "bits>=v", extra)
