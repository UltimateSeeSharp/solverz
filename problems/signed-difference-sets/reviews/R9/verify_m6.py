"""m = 6 candidate: GF(2^12) mod 0x1053, g = x; S = {x != 0 : log_g x mod 63 in T}; claimed NL_64(30) PDS
(4096,1950,926,930). Then P = G - 0 - S (NL_64(33)) and D = P - {0} should be SDS(4096, 2146, 1122).
Direct pair counting with numpy (no characters), plus the SDS autocorrelation on every shift."""
import numpy as np
MOD, D_ = 0x1053, 12
T = [0, 3, 6, 11, 12, 15, 21, 22, 24, 25, 27, 30, 31, 33, 37, 39, 42, 44, 45, 47, 48, 50, 51, 54, 55, 57, 59, 60, 61, 62]
def mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> D_ & 1: a ^= MOD
    return r
log = [-1] * 4096; x = 1
for i in range(4095):
    assert log[x] == -1; log[x] = i; x = mul(x, 2)
assert x == 1
S = np.array([y for y in range(1, 4096) if log[y] % 63 in T])
print("|S| =", len(S))
def diff_counts(A):
    cnt = np.zeros(4096, dtype=np.int64)
    for a in A:
        np.add.at(cnt, A ^ a, 1)
    return cnt
inS = np.zeros(4096, bool); inS[S] = True
c = diff_counts(S)
print("S: lambda values", sorted(set(c[1:][inS[1:]])), "mu values", sorted(set(c[1:][~inS[1:]])))
P = np.array([y for y in range(1, 4096) if not inS[y]])
inP = np.zeros(4096, bool); inP[P] = True
cP = diff_counts(P)
print("P: |P| =", len(P), "lambda", sorted(set(cP[1:][inP[1:]])), "mu", sorted(set(cP[1:][~inP[1:]])))
Dv = np.zeros(4096, dtype=np.int64); Dv[P] = 1; Dv[0] = -1
idx = np.arange(4096)
ac = np.array([int((Dv * Dv[idx ^ g]).sum()) for g in range(1, 4096)])
print("D support", int((Dv != 0).sum()), "autocorrelation values on all 4095 shifts:", sorted(set(ac)))
# Frobenius invariance of T and structure
print("T*2 mod 63 == T:", sorted(t * 2 % 63 for t in T) == sorted(T))
for d in (3, 7, 9, 21):
    print(f"T invariant under +{63//d} (union of cosets of order-{d} subgroup of GF(64)*):", sorted((t + 63 // d) % 63 for t in T) == sorted(T))
