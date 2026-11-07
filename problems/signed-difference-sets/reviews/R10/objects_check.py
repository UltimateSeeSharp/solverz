# Every object O*.txt: verify SDS, the rule must not fire on its parameters (in its own group),
# and on every coordinatewise quotient H with p !| |H|, exp(H) | p^i + 1, p^(2j) | n (j >= 1):
# coset sums congruent mod p^j (contract_congr_pow as read).
import re, glob, math, itertools, sys, numpy as np
sys.path.insert(0, sys.argv[1] + "/reviews/R10")
PF = sys.argv[1]
def pf(n):
    out, p = {}, 2; n = abs(n)
    while p * p <= n:
        while n % p == 0: out[p] = out.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out
def selfconj(p, e):  # exists i >= 1 with e | p^i + 1
    x = p % e
    for i in range(1, 2 * e + 2):
        if (x + 1) % e == 0: return i
        x = x * p % e
    return None
def divs(m): return [d for d in range(1, m + 1) if m % d == 0]
def mine(v, k, lam, ms, allow_odd=False):
    n = k - lam
    if n == 0: return None
    for p, e in pf(n).items():
        J = e // 2 if not allow_odd else max(e // 2, 1)
        if J == 0: continue
        for ds in itertools.product(*[divs(m) for m in ms]):
            h = math.prod(ds)
            if h == 1 or h % p == 0: continue
            if 2 * (v // h) >= p ** J: continue
            i = selfconj(p, math.lcm(*ds))
            if i: return (p, J, i, ds)
    return None
tests = fired = 0
for f in sorted(glob.glob(PF + "/objects/O*.txt"), key=lambda s: int(re.search(r"O(\d+)", s).group(1))):
    L = open(f, encoding="utf-8").read().split("\n")
    m = re.match(r"(\S+)\s+\((\d+),\s*(\d+),\s*(-?\d+)\)", L[0]); shape = [int(x) for x in re.findall(r"\d+", m.group(1))]
    v, k, lam = int(m.group(2)), int(m.group(3)), int(m.group(4)); assert math.prod(shape) == v
    A = np.zeros(shape, np.int64)
    for l in L[1:]:
        t = l.split()
        if not t: continue
        A[tuple(int(x) for x in t[:-1])] = 1 if t[-1] == "+" else -1
    F = np.fft.fftn(A); ac = np.rint(np.fft.ifftn(F * np.conj(F)).real).astype(np.int64)
    z = (0,) * len(shape); off = ac.copy(); off[z] = lam
    ok = int((A != 0).sum()) == k and ac[z] == k and (off == lam).all()
    f_rule = mine(v, k, lam, shape); fired += bool(f_rule)
    n = k - lam; bad = 0; t0 = tests
    for p, e in (pf(n).items() if n else []):
        if e < 2: continue
        for ds in itertools.product(*[divs(x) for x in shape]):
            h = math.prod(ds)
            if h == 1 or h % p == 0 or not selfconj(p, math.lcm(*ds)): continue
            a = np.zeros(ds, np.int64)
            for idx in itertools.product(*[range(x) for x in shape]):
                a[tuple(i % d for i, d in zip(idx, ds))] += A[idx]
            for j in range(1, e // 2 + 1):
                tests += 1; bad += int(((a - a.flat[0]) % p ** j != 0).any())
    print(f.split("\\")[-1].split("/")[-1], shape, (v, k, lam), "SDS" if ok else "NOT SDS", "rule:", f_rule, "tests", tests - t0, "bad", bad)
print("total congruence tests", tests, "rule fired on", fired)
