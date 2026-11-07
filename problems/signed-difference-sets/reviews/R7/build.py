"""Build each claimed set from its theorem and check it in the key's group (own code)."""
import itertools, sys
from sdscheck import check_direct, check_fft, split


def prime_divisors(m):
    return [f for f in range(2, m + 1) if m % f == 0 and all(f % g for g in range(2, int(f ** .5) + 1))]


class GF:
    """GF(p^n): elements are coefficient tuples (c0..c_{n-1}); additive group = Z_p^n as in the key."""

    def __init__(self, p, n):
        self.p, self.n, self.q = p, n, p ** n
        self.elems = list(itertools.product(range(p), repeat=n))
        self.zero = (0,) * n
        self.one = (1,) + (0,) * (n - 1)
        self.mod = None
        for tail in itertools.product(range(p), repeat=n):  # monic x^n + sum tail[i] x^i
            self.mod = tail
            g = self._primitive()
            if g is not None:  # an element of order q - 1 exists <=> the quotient ring is a field
                self.prim = g
                return
        raise ValueError("no field polynomial")

    def mul(self, a, b):
        p, n = self.p, self.n
        r = [0] * (2 * n - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    r[i + j] = (r[i + j] + x * y) % p
        for d in range(2 * n - 2, n - 1, -1):
            c = r[d]
            if c:
                r[d] = 0
                for i in range(n):
                    r[d - n + i] = (r[d - n + i] - c * self.mod[i]) % p
        return tuple(r[:n])

    def pow(self, a, e):
        r = self.one
        while e:
            if e & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            e >>= 1
        return r

    def _primitive(self):
        q1 = self.q - 1
        ps = prime_divisors(q1)
        for g in self.elems:
            if g != self.zero and self.pow(g, q1) == self.one and all(self.pow(g, q1 // f) != self.one for f in ps):
                return g
        return None

    def squares(self):
        return {self.mul(x, x) for x in self.elems if x != self.zero}


def report(name, D, mods, k, lam):
    ok1, bad = check_direct(D, mods, k, lam)
    ok2, err = check_fft(D, mods, k, lam)
    print(f"{name}: group Z{mods}, (|P|,|N|) = {split(D)}, direct={ok1} {bad[:2] if bad else ''} fft={ok2} (max dev {err:.1e})")
    return ok1 and ok2


def paley_and_zero(p, e):
    F = GF(p, e)
    v = F.q
    assert v % 4 == 3
    n = (v + 1) // 4
    sq = F.squares()
    assert len(sq) == (v - 1) // 2
    D = {x: 1 for x in sq}
    D[F.zero] = -1
    return report(f"Prop 2.3 v={v}={p}^{e} n={n} -> ({v},{2*n},{n-2}), poly tail {F.mod}", D, (p,) * e, 2 * n, n - 2)


def gordon41(q, r_p, r_e):
    """Thm 4.1, q prime, r = r_p^r_e = q + 6."""
    Fr = GF(r_p, r_e)
    assert Fr.q == q + 6
    m = (q + 3) // 2
    n = m * m
    chi_q = lambda x: 0 if x == 0 else (1 if pow(x, (q - 1) // 2, q) == 1 else -1)
    sqr = Fr.squares()
    chi_r = lambda y: 0 if y == Fr.zero else (1 if y in sqr else -1)
    D = {}
    for x in range(q):
        for y in Fr.elems:
            if chi_q(x) * chi_r(y) == 1 or (x == 0 and y != Fr.zero):
                D[(x,) + y] = 1
    D[(0,) + Fr.zero] = -1
    v, k, lam = 4 * n - 9, 2 * n - 1, n - 1
    ok = report(f"Thm 4.1 m={m} q={q} r={Fr.q} -> ({v},{k},{lam}) in Z{q} x GF({Fr.q})+, poly tail {Fr.mod}",
                D, (q,) + (r_p,) * r_e, k, lam)
    big = q * r_p  # key [5,95]: (x, y0, y1) -> (y0, z), z = x mod 19, z = y1 mod 5 (CRT isomorphism)
    crt = {(a, b): next(z for z in range(big) if z % q == a and z % r_p == b) for a in range(q) for b in range(r_p)}
    E = {(y0, crt[(x, y1)]): c for (x, y0, y1), c in D.items()}
    assert len(E) == len(D)
    ok2 = report("  mapped by CRT into the key's Z5 x Z95", E, (r_p, big), k, lam)
    return ok and ok2


def hcg55(q):
    """He-Chen-Ge Prop 5.5(2) in Z_q, q prime: P = G - Ci - Cj - 0, N = Ci + 0."""
    w = GF(q, 1).prim[0]
    f = (q - 1) // 4
    C = [{pow(w, 4 * j + i, q) for j in range(f)} for i in range(4)]
    k, lam = 3 * f + 1, (f - 5) // 4
    good = []
    for i in range(4):
        for j in range(4):
            if i != j:
                D = {(x,): 1 for x in set(range(q)) - C[i] - C[j] - {0}}
                D.update({(x,): -1 for x in C[i] | {0}})
                if check_direct(D, (q,), k, lam)[0]:
                    good.append((i, j))
    st = [(s, t) for s in range(-40, 41) for t in range(-40, 41)
          if s * s + t * t == q and s % 4 == 1 and s % q and (pow(w, f, q) * t - s) % q == 0]
    print(f"HCG 5.5(2) q={q} f={f} (f mod 4 = {f % 4}) w={w} (s,t)={st} -> ({q},{k},{(f - 5) / 4})")
    print("  ordered (i,j) giving an SDS by direct check:", good)
    if not good:
        return False
    i, j = good[0]
    D = {(x,): 1 for x in set(range(q)) - C[i] - C[j] - {0}}
    D.update({(x,): -1 for x in C[i] | {0}})
    return report(f"  (i,j)=({i},{j})", D, (q,), k, lam)


def hcg41_m2(x1):
    """He-Chen-Ge Thm 4.1 / Example 4.2: G = Z3 x Z3^2 x Z3^2; coefficients accumulated as group-ring sums."""
    G1 = list(itertools.product(range(3), repeat=2))
    Pp = {(1, 1), (2, 1), (1, 2), (2, 2)}
    Dp = {g: (1 if g in Pp else -1) for g in G1 if g != (0, 0)}
    report("  D' = P' - N' of Example 4.2", dict(Dp), (3, 3), 8, -1)
    coef = {}
    def acc(g, c):
        coef[g] = coef.get(g, 0) + c
    x0 = 1
    for g in G1:
        acc((x0, 0, 0) + g, 1)
        acc((0,) + g + tuple(x1), 1)
    for a, ca in Dp.items():
        for b, cb in Dp.items():
            acc((0,) + a + b, ca * cb)
    D = {g: c for g, c in coef.items() if c != 0}
    print(f"HCG Thm 4.1 m=2, x0=1, x1={x1}: coefficient values {sorted(set(coef.values()))}, nonzero {len(D)}")
    if any(abs(c) > 1 for c in D.values()):
        big = sorted(g for g, c in D.items() if abs(c) > 1)
        print(f"  NOT a signed set: coefficient 2 at {big}")
        return False
    return report("  ", D, (3,) * 5, 82, 1)


if __name__ == "__main__":
    which = sys.argv[1]
    if which == "paley":
        for p, e in [(211, 1), (223, 1), (239, 1), (251, 1), (263, 1), (271, 1), (419, 1), (3, 5), (7, 3),
                     (11, 1), (3, 3)]:  # last two are controls
            paley_and_zero(p, e)
    elif which == "g41":
        gordon41(19, 5, 2)
        gordon41(3, 3, 2)  # control: (27,17,8) in C3^3, credited by the importer
    elif which == "hcg55":
        hcg55(421)
        hcg55(29)  # control: f = 7, not 1 mod 4
    elif which == "hcg41":
        hcg41_m2((1, 0))
        hcg41_m2((0, 0))
