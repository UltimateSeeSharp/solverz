# Exact norm of u = (1 - x)^phi / p in Z[x]/(Phi_{p^j}): determinant of multiplication by u on the basis 1..x^(phi-1).
import math
from fractions import Fraction
def red(poly, q, p):
    s = q // p; phi = q - s; poly = poly[:] + [0] * max(0, 2 * q - len(poly))
    for t in range(len(poly) - 1, phi - 1, -1):
        c = poly[t]
        if c:
            poly[t] = 0
            for u in range(p - 1): poly[t - phi + u * s] -= c
    return poly[:phi]
def det(M):
    M = [[Fraction(x) for x in r] for r in M]; n = len(M); d = Fraction(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if M[r][i] != 0), None)
        if piv is None: return 0
        if piv != i: M[i], M[piv] = M[piv], M[i]; d = -d
        d *= M[i][i]
        for r in range(i + 1, n):
            f = M[r][i] / M[i][i]
            if f: M[r] = [a - f * b for a, b in zip(M[r], M[i])]
    return d
for p, j in [(2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3), (5, 1), (5, 2), (7, 1), (7, 2), (11, 1), (13, 1)]:
    q = p ** j; phi = q - q // p
    r = red([math.comb(phi, t) * (-1) ** t for t in range(phi + 1)], q, p)
    assert all(c % p == 0 for c in r); u = [c // p for c in r]
    cols = []
    for k in range(phi):
        prod = [0] * (2 * q)
        for a, c in enumerate(u): prod[a + k] += c
        cols.append(red(prod, q, p))
    M = [[cols[k][i] for k in range(phi)] for i in range(phi)]
    print(p, j, "N(u) =", det(M))
