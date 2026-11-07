# Weakest steps, exhaustively: (1) in F_p[K], ybar == y^(p^i) for every y when p^i = -1 mod exp K; (2) y*ybar = 0
# => y = 0 for every y in F_p[K] (claim cases, per-order-only cases, controls); (3) (1 - x)^phi = p * u in Z[zeta_{p^j}]
# with u a unit (exact: coefficients of (1-x)^phi mod Phi divisible by p, and |N(u)| = 1 by floating norm, rounded).
import itertools, math, cmath, collections
def sc(p, m): return m == 1 or any((pow(p, i, m) + 1) % m == 0 for i in range(1, m + 1))
def ring(p, K):
    kel = list(itertools.product(*[range(m) for m in K])); idx = {e: i for i, e in enumerate(kel)}
    add = [[idx[tuple((a + b) % m for a, b, m in zip(x, y, K))] for y in kel] for x in kel]
    neg = [idx[tuple((-a) % m for a, m in zip(x, K))] for x in kel]
    return kel, add, neg
def mul(p, add, y, z):
    out = [0] * len(y)
    for i, a in enumerate(y):
        if a:
            for j2, b in enumerate(z):
                if b: out[add[i][j2]] = (out[add[i][j2]] + a * b) % p
    return out
def test(p, K, label):
    kel, add, neg = ring(p, K); N = len(kel); m = math.lcm(*K) if K else 1
    i0 = next((i for i in range(1, m + 1) if (pow(p, i, m) + 1) % m == 0), None)
    frob_bad = 0; zd = 0
    for y in itertools.product(range(p), repeat=N):
        y = list(y); yb = [0] * N
        for i, a in enumerate(y): yb[neg[i]] = a
        if i0 is not None:
            z = y
            for _ in range(i0):  # z = z^p, p times multiplication
                w = z
                for _ in range(p - 1): w = mul(p, add, w, z)
                z = w
            if z != yb: frob_bad += 1
        if any(y) and not any(mul(p, add, y, yb)): zd += 1
    print(f"{label:14s} p={p} K={K} exp={m} sc(exp)={sc(p, m)} i={i0} frobenius mismatches={frob_bad} nonzero y with y*ybar=0: {zd}", flush=True)
for p, K, lab in [(2, [3], 'claim'), (2, [5], 'claim'), (2, [9], 'claim'), (2, [3, 3], 'claim'), (2, [11], 'claim'),
                  (2, [13], 'claim'), (2, [7], 'CONTROL'), (2, [15], 'per-order only'), (2, [3, 5], 'per-order only'),
                  (3, [2], 'claim'), (3, [4], 'claim'), (3, [2, 2], 'claim'), (3, [5], 'claim'), (3, [7], 'claim'),
                  (3, [8], 'CONTROL'), (3, [2, 4], 'claim'), (3, [10], 'claim'), (5, [3], 'claim'), (5, [6], 'claim'),
                  (5, [2, 2], 'claim'), (5, [4], 'CONTROL'), (7, [4], 'claim'), (7, [3], 'CONTROL'), (7, [2, 2], 'claim')]:
    if p ** math.prod(K) <= 2 * 10 ** 5: test(p, K, lab)
def cyclo_mod(poly, q, p):  # reduce poly (list, low first) mod Phi_q, q = p^j
    s = q // p; phi = q - s; poly = poly + [0] * max(0, q - len(poly))
    for t in range(len(poly) - 1, phi - 1, -1):
        c = poly[t]
        if c:
            poly[t] = 0
            for u in range(p): poly[t - phi + u * s] -= c  # x^t = x^(t-phi) * x^phi, x^phi = -sum_{u<p-1} x^{u s}
            poly[t] += c  # undo the u = p-1 term (that is x^t itself)
    return poly[:phi]
for p, j in [(2, 1), (2, 2), (2, 3), (2, 4), (3, 1), (3, 2), (3, 3), (5, 1), (5, 2), (7, 1), (11, 1), (13, 1)]:
    q = p ** j; phi = q - q // p
    poly = [math.comb(phi, t) * (-1) ** t for t in range(phi + 1)]
    r = cyclo_mod(poly, q, p)
    div = all(c % p == 0 for c in r); u = [c // p for c in r]
    nrm = 1
    for t in range(1, q + 1):
        if math.gcd(t, q) == 1:
            z = cmath.exp(2j * cmath.pi * t / q); nrm *= sum(c * z ** k for k, c in enumerate(u))
    print(f"p={p} j={j}: (1-x)^phi mod Phi divisible by p: {div}; N(u) = {nrm.real:.6f}")
