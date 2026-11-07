# Exact arithmetic in Z[zeta_q], q = p^J, for checking C22's intermediate claims (refuter, independent of r2/).
import math

def val(x, p):
    if x == 0:
        return 10**9
    x = abs(x); c = 0
    while x % p == 0:
        x //= p; c += 1
    return c

def ppow(x):
    """(p, J) with x = p^J, x > 1 a prime power."""
    p = 2
    while x % p:
        p += 1
    J = 0
    y = x
    while y % p == 0:
        y //= p; J += 1
    assert y == 1, x
    return p, J

def reduce(c, q):
    """c: list of length q (coeffs of zeta^0..zeta^{q-1}); return coeffs mod Phi_q, length phi(q)."""
    p, J = ppow(q)
    r = q // p          # p^{J-1}
    phi = r * (p - 1)
    c = list(c)
    # zeta^{(p-1)r + j} = -sum_{i=0}^{p-2} zeta^{i r + j}, j in [0, r)
    for j in range(r):
        top = c[(p - 1) * r + j]
        if top:
            for i in range(p - 1):
                c[i * r + j] -= top
            c[(p - 1) * r + j] = 0
    return c[:phi]

def mul(a, b, q):
    """a, b full-length-q coefficient lists; product as full-length-q list (exponents mod q)."""
    out = [0] * q
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    out[(i + j) % q] += x * y
    return out

def conj(a, q):
    out = [0] * q
    for i, x in enumerate(a):
        out[(-i) % q] += x
    return out

def det(M):
    """Bareiss fraction-free determinant of an integer matrix."""
    M = [row[:] for row in M]
    n = len(M)
    sign = 1
    prev = 1
    for k in range(n - 1):
        if M[k][k] == 0:
            sw = next((i for i in range(k + 1, n) if M[i][k] != 0), None)
            if sw is None:
                return 0
            M[k], M[sw] = M[sw], M[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[n - 1][n - 1]

def norm(a, q):
    """Norm from Q(zeta_q) to Q of the element with full-length-q coeffs a."""
    p, J = ppow(q)
    phi = (q // p) * (p - 1)
    cols = []
    for k in range(phi):
        sh = [0] * q
        for i, x in enumerate(a):
            sh[(i + k) % q] += x
        cols.append(reduce(sh, q))
    M = [[cols[k][i] for k in range(phi)] for i in range(phi)]
    return det(M)

def vpi(a, q):
    """Valuation at pi = 1 - zeta_q (q = p^J): v_p of the norm (pi totally ramified, residue degree 1)."""
    p, J = ppow(q)
    r = reduce(a, q)
    if all(x == 0 for x in r):
        return 10**9
    return val(norm(a, q), p)

if __name__ == "__main__":
    # self-tests: v_pi(1 - zeta) = 1, v_pi(p) = phi, norm(1-zeta)=p
    for q in [2, 3, 4, 5, 7, 8, 9, 16, 25, 27, 49]:
        p, J = ppow(q); phi = (q // p) * (p - 1)
        one_minus = [0] * q; one_minus[0] = 1; one_minus[1 % q] -= 1
        pp = [0] * q; pp[0] = p
        assert abs(norm(one_minus, q)) == p, (q, norm(one_minus, q))
        assert vpi(pp, q) == phi
        # 1 + zeta is a unit for p odd; for p = 2 it is associate to pi
        op = [0] * q; op[0] += 1; op[1 % q] += 1
        assert vpi(op, q) == (0 if p > 2 else (1 if q > 2 else 10**9)), (q, vpi(op, q))
        # sum of all zeta^i = 0
        assert vpi([1] * q, q) == 10**9
    print("cyc self-tests ok")
