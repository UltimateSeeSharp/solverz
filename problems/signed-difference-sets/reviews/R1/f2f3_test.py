"""F2/F3 numerically: for every SDS found by census on small groups, check translation/negation
(F2) and, for every homomorphism to small cyclic-product targets, the F3 identities."""
import itertools, math
def elems(sh): return list(itertools.product(*[range(m) for m in sh]))
def add(x, y, sh): return tuple((a + b) % m for a, b, m in zip(x, y, sh))
def corr(D, g, sh): return sum(D[x] * D[add(x, g, sh)] for x in D)
def is_sds(D, k, lam, sh):
    z = tuple(0 for _ in sh)
    return sum(1 for x in D if D[x]) == k and all(corr(D, g, sh) == lam for g in D if g != z)
def census(sh):
    E = elems(sh); z = tuple(0 for _ in sh); out = []
    for vals in itertools.product((-1, 0, 1), repeat=len(E)):
        D = dict(zip(E, vals)); c = {corr(D, g, sh) for g in E if g != z}
        if len(c) == 1: out.append((D, sum(1 for v in vals if v), c.pop()))
    return out
def homs(sh, th):
    """all homs Z_sh -> Z_th: images of generators e_i with order dividing sh[i]"""
    T = elems(th)
    def order(h): return math.lcm(*[m // math.gcd(a, m) for a, m in zip(h, th)])
    choices = [[h for h in T if sh[i] % order(h) == 0] for i in range(len(sh))]
    for imgs in itertools.product(*choices):
        def phi(x, imgs=imgs):
            r = tuple(0 for _ in th)
            for xi, h in zip(x, imgs):
                for _ in range(xi): r = add(r, h, th)
            return r
        yield phi
fails = 0; checks = 0
for sh, targets in [((3, 3), [(3,), (3, 3), (9,), (1,)]), ((2, 2, 2), [(2,), (2, 2), (4,), (2, 2, 2)]),
                    ((8,), [(2,), (4,), (8,), (2, 2)]), ((7,), [(7,), (1,)]), ((4, 2), [(2,), (4,), (2, 2)])]:
    E = elems(sh); z = tuple(0 for _ in sh)
    S = [s for s in census(sh) if s[1] > 0]
    for D, k, lam in S:
        for t in E:  # F2
            Dt = {x: D[add(x, t, sh)] for x in E}; Dn = {x: -D[x] for x in E}
            checks += 2; fails += (not is_sds(Dt, k, lam, sh)) + (not is_sds(Dn, k, lam, sh))
        for th in targets:  # F3
            H = elems(th); hz = tuple(0 for _ in th)
            for phi in homs(sh, th):
                img = {x: phi(x) for x in E}
                a = {h: sum(D[x] for x in E if img[x] == h) for h in H}
                fib = {h: sum(1 for x in E if img[x] == h) for h in H}
                for g2 in H:
                    ac = sum(a[h] * a[add(h, g2, th)] for h in H)
                    want = k + lam * (fib[hz] - 1) if g2 == hz else lam * fib[g2]
                    checks += 1; fails += ac != want
                for h in H:
                    checks += 1; fails += abs(a[h]) > fib[h]
    print(sh, "SDSs with k>0:", len(S), "params", sorted({(k, l) for _, k, l in S}))
print("checks", checks, "fails", fails)
