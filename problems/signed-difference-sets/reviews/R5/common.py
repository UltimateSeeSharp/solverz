"""Independent helpers (not importing the ideator's code): instances, multiplier group, orbits."""
import os, csv, re, math, ctypes
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"): os.environ[_v] = "1"
try:  # below-normal priority
    ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)
except Exception: pass
WT = "problems/signed-difference-sets"
IDEA = "problems/signed-difference-sets/scratch/ideator"
RSC = "problems/signed-difference-sets/reviews/R4"
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
def parse_key(key):
    m = KEY.fullmatch(key); v, k, lam = map(int, m.groups()[:3])
    return v, k, lam, tuple(int(x) for x in m.group(4).split(","))
def instances():
    with open(WT + "/instances.csv", encoding="utf-8", newline="") as f:
        return [(r["id"], r["key"], r["status"]) + parse_key(r["key"]) for r in csv.DictReader(f)]
def primes_of(n):
    n = abs(n); out = []; p = 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0: n //= p
        p += 1 if p == 2 else 2
    if n > 1: out.append(n)
    return out
def squarefree(n): return all((n // p) % p for p in primes_of(n))
def mult_group(n, e):
    """{t in Z_e^* : for every prime p | n, t = p^f mod e for some f >= 0}."""
    M = {t for t in range(e) if math.gcd(t, e) == 1}
    for p in primes_of(n):
        P = set(); x = 1 % e
        for _ in range(e + 1):
            P.add(x); x = x * p % e
        M &= P
    return M
def elements(shape):
    out = [()]
    for m in shape: out = [g + (x,) for g in out for x in range(m)]
    return out
def orbits(shape, M):
    """Orbits of x -> t x (t in M) on prod Z_m, as a label per element in row-major order."""
    els = elements(shape); strides = [math.prod(shape[i + 1:]) for i in range(len(shape))]
    ix = lambda g: sum(a * s for a, s in zip(g, strides))
    lab = [-1] * len(els); r = 0
    for j, g in enumerate(els):
        if lab[j] >= 0: continue
        for t in M: lab[ix(tuple(t * a % m for a, m in zip(g, shape)))] = r
        r += 1
    return lab, r
def invariant_type(shape):
    """Isomorphism type of prod Z_m as a sorted tuple of prime powers."""
    out = []
    for m in shape:
        for p in primes_of(m):
            q = 1
            while m % (q * p) == 0: q *= p
            out.append(q)
    return tuple(sorted(out))
