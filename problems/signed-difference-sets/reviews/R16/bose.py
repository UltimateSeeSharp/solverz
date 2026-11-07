"""Own code (independent of e10-objects): Bose affine RDS in GF(q^2), projection, R - H, SDS check."""
import itertools, sys, cmath

def prime_power(s):
    for p in range(2, s + 1):
        if s % p == 0:
            e, t = 0, s
            while t % p == 0:
                t //= p; e += 1
            return (p, e) if t == 1 else None
    return None

def gf_tables(p, e):
    """exp table of GF(p^e) as int codes (base p digits = coefficients), via a primitive polynomial."""
    Q = p ** e
    for tail in itertools.product(range(p), repeat=e):   # x^e = sum tail[j] x^j (mod p)
        if tail[0] == 0:
            continue
        cur = [1] + [0] * (e - 1)
        exp = []
        seen = set()
        ok = True
        for i in range(Q - 1):
            code = sum(c * p ** j for j, c in enumerate(cur))
            if code in seen:
                ok = False; break
            seen.add(code); exp.append(code)
            top = cur[-1]                                  # multiply by x
            cur = [0] + cur[:-1]
            cur = [(cur[j] + top * tail[j]) % p for j in range(e)]
        if ok and cur == [1] + [0] * (e - 1):
            return exp, tail
    raise ValueError("no primitive polynomial")

def add(a, b, p, e):
    r, m = 0, 1
    for _ in range(e):
        r += ((a % p + b % p) % p) * m
        a //= p; b //= p; m *= p
    return r

def bose(q, p, e2):
    """R = {i in Z_{q^2-1} : a^i + a^(iq) = 1} in GF(q^2) = GF(p^e2)."""
    exp, tail = gf_tables(p, e2)
    N = q * q - 1
    assert len(exp) == N
    return [i for i in range(N) if add(exp[i], exp[(i * q) % N], p, e2) == 1], tail

def diff_counts(S, v):
    c = [0] * v
    for a in S:
        for b in S:
            c[(a - b) % v] += 1
    return c

def is_rds(S, v, m):
    """S in Z_v relative to H = multiples of m (|H| = v/m): 0 on H\0, constant on G\H; returns that constant or None."""
    c = diff_counts(S, v)
    if any(c[g] for g in range(m, v, m)):
        return None
    vals = {c[g] for g in range(1, v) if g % m}
    return vals.pop() if len(vals) == 1 else None

def autocorr(D, v):
    return [sum(D[x] * D[(x + g) % v] for x in range(v)) for g in range(v)]

def sds_direct(D, v, k, lam):
    if sum(1 for d in D if d) != k or any(d not in (-1, 0, 1) for d in D):
        return False
    a = autocorr(D, v)
    return a[0] == k and all(a[g] == lam for g in range(1, v))

def sds_dft(D, v, k, lam):
    """|D^(chi)|^2 = k - lam for every nontrivial chi of Z_v; D^(1)^2 = k + lam(v-1)."""
    worst = 0.0
    for j in range(v):
        z = sum(D[x] * cmath.exp(2j * cmath.pi * j * x / v) for x in range(v) if D[x])
        target = k + lam * (v - 1) if j == 0 else k - lam
        worst = max(worst, abs(abs(z) ** 2 - target))
    return worst

def family_member(s):
    """n = s - 1, q = s^2: returns v, k, lam, D (in Z_v), Rbar, missed coset."""
    p, e = prime_power(s)
    n, q = s - 1, s * s
    R, tail = bose(q, p, 4 * e)
    return n, q, R, tail
