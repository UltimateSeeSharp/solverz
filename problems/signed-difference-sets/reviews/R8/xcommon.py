"""Independent helpers (refuter, extensions). Own quotient types, self-conjugacy, factoring."""
import csv, re, math
WT = "problems/signed-difference-sets"
SCR = "problems/signed-difference-sets/scratch"
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

def parse(key):
    m = KEY.fullmatch(key)
    v, k, lam = int(m[1]), int(m[2]), int(m[3])
    shape = [int(x) for x in m[4].split(",")]
    assert math.prod(shape) == v
    return v, k, lam, shape

def rows():
    with open(WT + "/instances.csv", encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))

def primefac(n):
    out = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1; n //= d
        d += 1 if d == 2 else 2
    if n > 1: out[n] = out.get(n, 0) + 1
    return out

def _subdiagrams(lam):
    """Non-increasing mu with mu_i <= lam_i (lam non-increasing), padded with zeros."""
    res = []
    def rec(i, cap, cur):
        if i == len(lam):
            res.append(tuple(cur)); return
        for x in range(min(cap, lam[i]), -1, -1):
            rec(i + 1, x, cur + [x])
    rec(0, max(lam) if lam else 0, [])
    return res

def quotient_types(shape):
    """Set of (order, exponent) over all isomorphism types of quotients of prod Z_shape."""
    per = {}
    for m in shape:
        for q, e in primefac(m).items():
            per.setdefault(q, []).append(e)
    types = {(1, 1)}
    for q, lam in per.items():
        lam = sorted(lam, reverse=True)
        opts = {(q ** sum(mu), q ** (mu[0] if mu else 0)) for mu in _subdiagrams(lam)}
        types = {(a * b, x * y) for (a, x) in types for (b, y) in opts}
    return types

def self_conj(p, m):
    """-1 in <p> mod m (p prime, gcd(p, m) = 1 required)."""
    if math.gcd(p, m) != 1: return False
    if m <= 2: return True
    seen, x = set(), 1
    while True:
        x = x * p % m
        if x in seen: break
        seen.add(x)
    return (m - 1) in seen

def s_of(v, k, lam):
    S = k - lam + lam * v
    if S < 0: return None
    s = math.isqrt(S)
    return s if s * s == S else None
