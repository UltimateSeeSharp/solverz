# Known SDS built from scratch: Singer, Paley and twin-prime-power difference sets (and their
# complements), a brute-forced CW(13,9) and Kronecker products of group weighing matrices.
import itertools, math, numpy as np
from indep import factor

def gf(p, e):
    """GF(p^e) as int-encoded polynomials over F_p with a primitive modulus; returns mul, pow."""
    N = p ** e - 1
    def dec(x): return [(x // p ** i) % p for i in range(e)]
    def enc(c): return sum(ci * p ** i for i, ci in enumerate(c))
    for f in itertools.product(range(p), repeat=e):
        if f[0] == 0: continue
        def mul(a, b, f=f):
            A, B = dec(a), dec(b); r = [0] * (2 * e - 1)
            for i, x in enumerate(A):
                if x:
                    for j, y in enumerate(B): r[i + j] = (r[i + j] + x * y) % p
            for i in range(2 * e - 2, e - 1, -1):  # x^e = -sum f_i x^i
                t = r[i]
                if t:
                    r[i] = 0
                    for j in range(e): r[i - e + j] = (r[i - e + j] - t * f[j]) % p
            return enc(r[:e])
        def pw(a, n, mul=mul):
            r = 1
            while n:
                if n & 1: r = mul(r, a)
                a = mul(a, a); n >>= 1
            return r
        x = p if e > 1 else None
        if e == 1: continue
        if pw(x, N) == 1 and all(pw(x, N // r) != 1 for r in factor(N)):
            return mul, pw, x, enc, dec
    raise ValueError

def add(a, b, p, e):
    return sum(((a // p ** i + b // p ** i) % p) * p ** i for i in range(e))

def singer(q, d):
    p, a = next(iter(factor(q).items())); e = a * d
    mul, pw, x, enc, dec = gf(p, e)
    v = (q ** d - 1) // (q - 1)
    D, y = [], 1
    for i in range(v):
        t, z = 0, y
        for _ in range(d):  # Tr_{q^d/q}(y) = y + y^q + ... + y^{q^{d-1}}
            t = add(t, z, p, e); z = pw(z, q)
        if t == 0: D.append(i)
        y = mul(y, x)
    k = len(D); lam = k * (k - 1) // (v - 1)
    return [v], k, lam, D

def qr(q): return {x * x % q for x in range(1, q)}

def arr(shape, plus, minus=()):
    A = np.zeros(shape, dtype=np.int64)
    for g in plus: A[g] = 1
    for g in minus: A[g] = -1
    return A

def complement(shape, k, lam, A):
    v = math.prod(shape); B = 1 - A
    return shape, v - k, v - 2 * k + lam, B

def cw13_9():
    for S in itertools.combinations(range(13), 9):
        for sg in itertools.product((1, -1), repeat=8):
            A = np.zeros(13, dtype=np.int64); A[list(S)] = (1,) + sg
            if all(int((A * np.roll(A, -g)).sum()) == 0 for g in range(1, 13)): return A
    raise ValueError

def all_sets():
    out = []
    for q, d in [(2, 3), (3, 3), (4, 3), (5, 3), (7, 3), (8, 3), (9, 3), (11, 3), (13, 3), (16, 3),
                 (17, 3), (19, 3), (23, 3), (25, 3), (27, 3), (2, 4), (3, 4), (4, 4), (5, 4),
                 (2, 5), (3, 5), (2, 6), (2, 7), (2, 8), (3, 6)]:
        sh, k, lam, D = singer(q, d); out.append((f"C:Singer({q},{d})", sh, k, lam, arr(sh, [(i,) for i in D])))
    for q in range(7, 1000):
        if q % 4 == 3 and len(factor(q)) == 1 and factor(q).get(q) == 1:
            Q = qr(q); out.append((f"C:Paley({q})", [q], len(Q), (q - 3) // 4, arr([q], [(x,) for x in Q])))
    for q in (3, 5, 11, 17, 29):
        r = q + 2; Qq, Qr = qr(q), qr(r)
        chi = lambda x, Q: 1 if x in Q else -1
        D = [(x, y) for x in range(1, q) for y in range(1, r) if chi(x, Qq) * chi(y, Qr) == 1] + [(x, 0) for x in range(q)]
        v = q * r; out.append((f"C:TwinPrime({q},{r})", [q, r], len(D), (v - 3) // 4, arr([q, r], D)))
    # (7,9): Z7 x GF(9), GF(9) = F3[i]/(i^2+1) as Z3 x Z3 coordinates (a + b i)
    sq9 = {((a * a - b * b) % 3, (2 * a * b) % 3) for a in range(3) for b in range(3) if (a, b) != (0, 0)}
    Q7 = qr(7)
    D = [(x, a, b) for x in range(1, 7) for a in range(3) for b in range(3) if (a, b) != (0, 0)
         and (x in Q7) == ((a, b) in sq9)] + [(x, 0, 0) for x in range(7)]
    out.append(("C:TwinPrime(7,9)", [7, 3, 3], len(D), 15, arr([7, 3, 3], D)))
    for q in range(7, 1000):  # Paley and zero: QR - {0} (q, (q+1)/2, (q-7)/4), QR + {0} (q, (q+1)/2, (q+1)/4)
        if q % 4 == 3 and len(factor(q)) == 1 and factor(q).get(q) == 1:
            Q = [(x,) for x in qr(q)]
            out.append((f"C:PaleyMinusZero({q})", [q], len(Q) + 1, (q - 7) // 4, arr([q], Q, [(0,)])))
            out.append((f"C:PaleyPlusZero({q})", [q], len(Q) + 1, (q + 1) // 4, arr([q], Q + [(0,)])))
    for sh in ([5], [9], [3, 3], [11], [13], [25], [5, 5], [27], [3, 9], [3, 3, 3], [15], [21], [45], [3, 15]):
        v = math.prod(sh); A = np.ones(sh, dtype=np.int64); A[(0,) * len(sh)] = -1  # (v, v, v-4)
        out.append((f"C:Trivial{sh}", sh, v, v - 4, A))
    out += [(n + "^c", *complement(sh, k, lam, A)) for n, sh, k, lam, A in list(out) if A.min() >= 0 and (A != 1).any()]
    # group weighing matrices (lam = 0) and Kronecker products
    W = {"CW(13,9)": ([13], 9, cw13_9()), "CW(7,4)": ([7], 4, arr([7], [(1,), (2,), (4,)], [(0,)])),
         "CW(4,4)": ([4], 4, arr([4], [(1,), (2,), (3,)], [(0,)])), "CW(2,2)": ([2], 2, arr([2], [(0,), (1,)])) }
    W["CW(2,2)"] = ([2], 2, np.array([1, 1]))  # (1,1): autocorrelation at 1 is 2, not 0 -> drop
    del W["CW(2,2)"]
    for n1, (s1, k1, A1) in W.items():
        out.append((f"C:{n1}", s1, k1, 0, A1))
    for (n1, (s1, k1, A1)), (n2, (s2, k2, A2)) in itertools.combinations_with_replacement(W.items(), 2):
        out.append((f"C:{n1}x{n2}", s1 + s2, k1 * k2, 0, np.multiply.outer(A1, A2)))
    for n1, (s1, k1, A1) in W.items():  # triple products with CW(7,4) and CW(4,4)
        for n2, n3 in [("CW(7,4)", "CW(4,4)"), ("CW(13,9)", "CW(4,4)")]:
            s2, k2, A2 = W[n2]; s3, k3, A3 = W[n3]
            out.append((f"C:{n1}x{n2}x{n3}", s1 + s2 + s3, k1 * k2 * k3, 0, np.multiply.outer(np.multiply.outer(A1, A2), A3)))
    return out
