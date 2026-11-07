"""On every object: verify SDS; for each cyclic quotient ZMod m with gcd(m,n)=1 (a few surjective forms), check C10
(a translate of the coset sums fixed by the whole multiplier group), the descent identity chi_a(Y)=chi_a(Y_S) and the
C27 bound for every admissible F."""
import sys, re, glob, cmath, itertools, random
from math import gcd, prod, lcm
from functools import reduce
from scan_exists import factor, totient, gen_sub
random.seed(1)
root = sys.argv[1]
stats = dict(objs=0, quot=0, c10_ok=0, c10_fail=0, bound_tests=0, bound_fail=0, chi_fail=0, tight=0)
for path in sorted(glob.glob(root + "/objects/O*.txt")):
    lines = open(path, encoding="utf-8").read().split("\n")
    hdr = re.match(r"(\S+) \((\d+),(\d+),(-?\d+)\)", lines[0])
    ms = [int(x) for x in hdr.group(1).replace("C", "").split("x")]
    v, k, lam = int(hdr.group(2)), int(hdr.group(3)), int(hdr.group(4))
    D = {}
    for ln in lines[1:]:
        ln = ln.strip()
        if not ln: continue
        *xs, s = ln.split()
        D[tuple(int(x) for x in xs)] = 1 if s == "+" else -1
    assert prod(ms) == v and len(D) == k, path
    els = list(itertools.product(*[range(x) for x in ms]))
    # SDS check (sparse)
    for g in random.sample(els, min(len(els), 30)):
        if all(x == 0 for x in g): continue
        tot = sum(s * D.get(tuple((a + b) % q for a, b, q in zip(x, g, ms)), 0) for x, s in D.items())
        assert tot == lam, (path, g, tot)
    stats["objs"] += 1
    n = k - lam
    w = reduce(lcm, ms)
    for m in range(2, w + 1):
        if w % m or gcd(m, n) != 1: continue
        forms = set()
        # CRT-type forms and random ones: a_i with m | a_i * ms_i; surjective iff gcd of a_i (mod m) with m is 1
        for _ in range(6):
            A = tuple(random.randrange(0, m, m // gcd(m, q)) for q in ms)
            if reduce(gcd, list(A) + [m]) == 1: forms.add(A)
        for A in forms:
            stats["quot"] += 1
            c = v // m
            Y = [0] * m
            for x, s in D.items(): Y[sum(a * xi for a, xi in zip(A, x)) % m] += s
            assert all(abs(y) <= c for y in Y)
            M = None
            for p in factor(n):
                S = gen_sub(p, m); M = S if M is None else M & S
            if M is None: M = {t for t in range(m) if gcd(t, m) == 1}
            bs = [b for b in range(m) if all(Y[(t * h + b) % m] == Y[(h + b) % m] for t in M for h in range(m))]
            if not bs:
                stats["c10_fail"] += 1; print("C10 FAIL", path, m, A); continue
            stats["c10_ok"] += 1
            Yb = [Y[(h + bs[0]) % m] for h in range(m)]
            for F in range(1, m + 1):
                if m % F: continue
                if not all(gcd(1 + F * u, m) == 1 and (1 + F * u) % m in M for u in range(m // F)): continue
                stats["bound_tests"] += 1
                if totient(m) * n > m * F * c * c: stats["bound_fail"] += 1; print("BOUND FAIL", path, m, F)
                if totient(m) * n == m * F * c * c: stats["tight"] += 1
                for a in range(1, m):
                    if gcd(a, m) != 1: continue
                    z = cmath.exp(2j * cmath.pi / m)
                    x1 = sum(Yb[h] * z ** (a * h % m) for h in range(m))
                    x2 = sum(Yb[h] * z ** (a * h % m) for h in range(m) if F * h % m == 0)
                    if abs(x1 - x2) > 1e-6 or abs(abs(x1) ** 2 - n) > 1e-6:
                        stats["chi_fail"] += 1; print("CHI FAIL", path, m, F, a, x1, x2); break
print(stats)
