"""He-Wu's four obstructions (as in their count_open_cases.py), own code, on the rows here."""
from math import gcd, isqrt
def fac(n):
    out, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out
def selfconj(n, e):
    for p, a in fac(n).items():
        if a % 2 == 0: continue
        for m in range(2, e + 1):
            if e % m or gcd(p, m) != 1: continue
            x = 1
            for j in range(1, m + 1):
                x = x * p % m
                if x == m - 1: return (p, m, j)
    return None
for v, k, lam in [(79,61,38),(127,109,90),(217,193,168),(222,69,20),(455,71,7),(300,55,6)]:
    n = k - lam
    c2 = v % 2 == 0 and isqrt(n) ** 2 != n
    near = k == v - 1
    print((v, k, lam), "n", n, "selfconj", selfconj(n, v), "C2-quotient", c2,
          "near-full applies", near, "small-defect applies", False, "s^2=k+lam(v-1):",
          isqrt(k + lam * (v - 1)) ** 2 == k + lam * (v - 1))
