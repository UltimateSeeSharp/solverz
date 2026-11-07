"""Compare the Frobenius-invariant norm-class NL solutions T (m = 4: t = 9; m = 6: t = 30) by trace features."""
import sys
def run(d, mod, T, label):
    m = d // 2
    def mul(a, b):
        r = 0
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if a >> d & 1: a ^= mod
        return r
    def pw(a, e):
        r = 1
        while e:
            if e & 1: r = mul(r, a)
            a = mul(a, a); e >>= 1
        return r
    q = 1 << m
    h = pw(2, q + 1)                  # generator of GF(q)* = norm of g
    def tr(a, k):                     # Tr_{GF(q)/GF(2^k)}
        s, z = 0, a
        for _ in range(m // k): s ^= z; z = pw(z, 2 ** k)
        return s
    one = 1
    w = pw(h, (q - 1) // 3)           # primitive cube root of unity (GF(4)*)
    name = {0: "0", 1: "1", w: "w", mul(w, w): "w2"}
    from collections import Counter
    c_in, c_out = Counter(), Counter()
    for i in range(q - 1):
        a = pw(h, i)
        key = (tr(a, 1), name.get(tr(a, 2), "?"))
        (c_in if i in T else c_out)[key] += 1
    print(label, "in T:", sorted(c_in.items()), "| not in T:", sorted(c_out.items()))
run(8, 0x11D, {0, 1, 2, 3, 4, 6, 8, 9, 12}, "m=4 (mod 0x11d)")
run(12, 0x1053, {0, 3, 6, 11, 12, 15, 21, 22, 24, 25, 27, 30, 31, 33, 37, 39, 42, 44, 45, 47, 48, 50, 51, 54, 55, 57, 59, 60, 61, 62}, "m=6 (mod 0x1053)")
