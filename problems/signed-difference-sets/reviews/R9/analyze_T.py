"""Structure of the m = 6 set T (norm values in GF(64)) found by cyc."""
MOD, D_ = 0x1053, 12
T = [0, 3, 6, 11, 12, 15, 21, 22, 24, 25, 27, 30, 31, 33, 37, 39, 42, 44, 45, 47, 48, 50, 51, 54, 55, 57, 59, 60, 61, 62]
def mul(a, b, mod=MOD, d=D_):
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
h = pw(2, 65)                         # norm of g: generator of GF(64)* inside GF(4096)
F64 = [0] + [pw(h, i) for i in range(63)]
assert len(set(F64)) == 64
def tr64(a):                          # absolute trace GF(64) -> GF(2), computed as a + a^2 + ... + a^32
    s, z = 0, a
    for _ in range(6): s ^= z; z = mul(z, z)
    return s
Tv = {pw(h, t) for t in T}
print("traces of T:", sorted(tr64(a) for a in Tv).count(0), "with Tr=0,", sorted(tr64(a) for a in Tv).count(1), "with Tr=1")
# additive structure inside GF(64) viewed as GF(2)^6 (elements are field elements; XOR = addition)
lam = {}
for g in F64[1:]:
    c = sum(1 for a in Tv if (a ^ g) in Tv)
    lam.setdefault(g in Tv, set()).add(c)
print("difference counts of T in (GF(64),+):", lam)
# subfields
F4 = {a for a in F64 if mul(a, mul(a, mul(a, a))) == a}      # a^4 = a
F8 = {a for a in F64 if pw(a, 8) == a}
print("|T cap GF(4)*| =", len(Tv & F4), " |T cap GF(8)*| =", len(Tv & F8))
miss = [a for a in F64[1:] if a not in Tv]
print("complement (33 elems) traces:", [tr64(a) for a in miss].count(0), "zero")
# relative traces / norms to subfields
def tr_to(a, k):  # Tr_{64/2^k}
    s, z = 0, a
    for _ in range(6 // k): s ^= z; z = pw(z, 2 ** k)
    return s
for k in (2, 3):
    from collections import Counter
    print(f"Tr_64/{2**k} on T:", Counter(tr_to(a, k) for a in Tv).most_common(), "| on complement:", Counter(tr_to(a, k) for a in miss).most_common())
# cube map and 7th power (norms to GF(4)*, GF(8)*)
from collections import Counter
print("N_64/4 = a^21 on T:", Counter(pw(a, 21) for a in Tv), "on comp:", Counter(pw(a, 21) for a in miss))
print("N_64/8 = a^9 on T:", Counter(pw(a, 9) for a in Tv), "on comp:", Counter(pw(a, 9) for a in miss))
# inverses
print("T closed under inverse:", {pw(a, 62) for a in Tv} == Tv)
