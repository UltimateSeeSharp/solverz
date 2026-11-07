# Independent mirror of ScCert.Valid / ScCert.Kills / MomentsOk, written from the Lean text
# (SelfConjugacyCheck.lean, Moments.lean). Lean Int `/` and `%` are Euclidean (ediv/emod).
import math, itertools

def ediv(a, b):  # Lean Int.ediv
    q = a // b if b > 0 else -(a // -b)
    return q if a - b * q >= 0 else q + (1 if b < 0 else -1)

def emod(a, b):
    return a - b * ediv(a, b)

def dvd(a, b):  # a | b in Z (Int.dvd: 0 | b iff b = 0)
    return b == 0 if a == 0 else b % a == 0

def moments_ok(N, q, sp, Q, t0):
    if not dvd(q, sp - N * t0): return False
    if not dvd(q * q, Q - 2 * t0 * sp + N * t0 ** 2): return False
    S1 = ediv(sp - N * t0, q)
    S2 = ediv(Q - 2 * t0 * sp + N * t0 ** 2, q ** 2)
    m = ediv(S1, N)
    B = S2 - 2 * m * S1 + N * m * m
    return emod(S2 - S1, 2) == 0 and S1 - N * m <= B and B != 0

def is_prime_td(p):
    return p >= 2 and all(p % d != 0 for d in range(2, p))

def valid(ms, k, lam, p, j, i, ds):
    return (is_prime_td(p) and 0 < i and all(m > 0 for m in ms) and len(ds) == len(ms)
            and all(m % d == 0 if d else m == 0 for d, m in zip(ds, ms))
            and all(dvd(d, p ** i + 1) for d in ds) and not dvd(p, math.prod(ds))
            and 1 < math.prod(ds) and dvd(p ** (2 * j), k - lam) and k != lam)

def kills(ms, k, lam, p, j, i, ds, s):
    if not valid(ms, k, lam, p, j, i, ds): return False
    v, h = math.prod(ms), math.prod(ds)
    c = v // h
    if 2 * c < p ** j: return "C5"
    if s * s != k + lam * (v - 1): return False
    Q = k + lam * (c - 1)
    if all(not moments_ok(h, p ** j, sp, Q, t) for sp in (s, -s) for t in range(p ** j)):
        return "C6"
    return False

def factor(n):
    f, q = {}, 2
    n = abs(n)
    while q * q <= n:
        while n % q == 0: f[q] = f.get(q, 0) + 1; n //= q
        q += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def all_certs(ms, k, lam):
    """Every certificate the Lean theorem admits (any p with p^2 | n, any 1 <= j <= v_p/2, any
    coordinatewise ds, least i), with s = +isqrt (the sign is tested both ways anyway)."""
    n = k - lam
    if n == 0: return
    v = math.prod(ms)
    S = k + lam * (v - 1)
    s = math.isqrt(S) if S >= 0 and math.isqrt(S) ** 2 == S else 0
    for p, e in factor(n).items():
        for j in range(1, e // 2 + 1):
            for ds in itertools.product(*[[d for d in range(1, m + 1) if m % d == 0] for m in ms]):
                h = math.prod(ds)
                if h == 1 or h % p == 0: continue
                L = math.lcm(*ds)
                i = next((i for i in range(1, 2 * L + 2) if (p ** i + 1) % L == 0), None)
                if i is None: continue
                yield (p, j, i, list(ds), s)

def box_ok(N, q, sp, Q, t0, c):  # Lean BoxOk (Box.lean)
    if not moments_ok(N, q, sp, Q, t0): return False
    S2 = ediv(Q - 2 * t0 * sp + N * t0 ** 2, q ** 2)
    S1 = ediv(sp - N * t0, q)
    return S2 <= (-ediv(c + t0, q) + ediv(c - t0, q)) * S1 + N * ediv(c + t0, q) * ediv(c - t0, q)

def box_kills(ms, k, lam, p, j, i, ds, s):  # Lean ScCert.BoxKills (BoxCheck.lean)
    if not valid(ms, k, lam, p, j, i, ds): return False
    v, h = math.prod(ms), math.prod(ds)
    c = v // h
    if s * s != k + lam * (v - 1): return False
    return all(not box_ok(h, p ** j, sp, k + lam * (c - 1), t, c) for sp in (s, -s) for t in range(p ** j))
