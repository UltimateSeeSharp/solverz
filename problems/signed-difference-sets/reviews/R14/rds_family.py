"""Family: R = Bose affine RDS {x in GF(q^2)*: Tr(x)=1}, q=(n+1)^2, projected to Z_{(q+1)n};
D = R - H (H = image of GF(q)*, order n). Claim: (n(q+1), q+n, n) SDS. Check n=2,3,4,6,7."""
import itertools, sys
sys.path.insert(0, ".")

def polymulmod(a, b, mod, p):
    d = len(mod) - 1
    res = [0] * (2 * d)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                res[i + j] = (res[i + j] + x * y) % p
    for i in range(2 * d - 1, d - 1, -1):
        c = res[i]
        if c:
            for j in range(d + 1):
                res[i - d + j] = (res[i - d + j] - c * mod[j]) % p
    return res[:d]

def field(p, e):
    N = p ** e - 1
    for coeffs in itertools.product(range(p), repeat=e):
        mod = list(coeffs) + [1]  # monic, low degree first
        if mod[0] == 0:
            continue
        x = [0, 1] + [0] * (e - 2) if e > 1 else [0]
        cur = [1] + [0] * (e - 1)
        seen = {}
        ok = True
        for i in range(N):
            t = tuple(cur)
            if t in seen:
                ok = False
                break
            seen[t] = i
            cur = polymulmod(cur, x, mod, p)
        if ok and tuple(cur) == tuple([1] + [0] * (e - 1)) and len(seen) == N:
            return mod, seen  # seen: element tuple -> log
    raise ValueError

def build(n, p, e):
    q = (n + 1) ** 2
    assert p ** e == q * q
    mod, log = field(p, e)
    N = q * q - 1
    exp = {i: t for t, i in log.items()}
    one = tuple([1] + [0] * (e - 1))
    R = []
    for i in range(N):
        a, b = exp[i], exp[(i * q) % N]
        s = tuple((x + y) % p for x, y in zip(a, b))
        if s == one:
            R.append(i)
    assert len(R) == q
    v = (q + 1) * n
    D = [0] * v
    for i in R:
        D[i % v] += 1
    for j in range(n):
        D[(j * (q + 1)) % v] -= 1
    return v, q + n, n, D

def is_sds(v, k, lam, D):
    if any(d not in (-1, 0, 1) for d in D) or sum(1 for d in D if d) != k:
        return False
    return all(sum(D[x] * D[(x + g) % v] for x in range(v)) == lam for g in range(1, v))

if __name__ == "__main__":
    for n, p, e in [(2, 3, 4), (3, 2, 8), (4, 5, 4), (6, 7, 4), (7, 2, 12)]:
        v, k, lam, D = build(n, p, e)
        print((v, k, lam), "coeffs in {-1,0,1}:", all(d in (-1, 0, 1) for d in D),
              "SDS:", is_sds(v, k, lam, D), "+", D.count(1), "-", D.count(-1))
        if n == 6:
            open("sds_300_55_6.txt", "w").write(f"C300 (300,55,6)\n" + "".join(
                f"{x} {'+' if D[x] == 1 else '-'}\n" for x in range(v) if D[x]))
