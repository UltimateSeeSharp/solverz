# N79/N80 (a): exhaustive coset-sum vectors on C3 x C3 (and C9) for (27,22,9) with fibres of 3,
# WITHOUT the abs/parity demands: entries in [-3,3], sum 16 (sum -16 is the negation), sum of squares 40,
# autocorrelation 27 at every nonzero shift.
import itertools, sys
def search(elems, add, cap, S, Q, mu):
    n = len(elems); sols = []
    a = [0] * n
    def rec(i, s, q):
        if i == n:
            if s == S and q == Q: check()
            return
        rem = n - i
        for x in range(-cap, cap + 1):
            s2, q2 = s + x, q + x * x
            if abs(S - s2) > cap * (rem - 1) or q2 > Q: continue
            # remaining squares must reach sum gap: need (S-s2)^2 <= (rem-1)*(Q-q2) (Cauchy-Schwarz)
            if (rem - 1) == 0:
                if s2 != S or q2 != Q: continue
            elif (S - s2) ** 2 > (rem - 1) * (Q - q2): continue
            a[i] = x; rec(i + 1, s2, q2)
    def check():
        for g in range(1, n):
            if sum(a[h] * a[add[h][g]] for h in range(n)) != mu: return
        sols.append(tuple(a))
    rec(0, 0, 0)
    return sols
def grp(ms):
    elems = list(itertools.product(*[range(m) for m in ms]))
    idx = {e: i for i, e in enumerate(elems)}
    add = [[idx[tuple((x + y) % m for x, y, m in zip(e, f, ms))] for f in elems] for e in elems]
    return elems, add
cnt = 0
for ms in ([3, 3], [9]):
    e, add = grp(ms)
    sols = search(e, add, 3, 16, 40, 27)
    print("H =", ms, "vectors:", len(sols), sols[:3])
# positive control: (13,9,6)? use a real SDS contraction: Paley-type (9,8,-1) in C3xC3 -> C3 (fibre 3):
e, add = grp([3])
# (9,8,-1): s^2 = 8 - 8 = 0, S = 0; contraction to C3: sum sq = k + lam*(3-1) = 8 - 2 = 6, corr = lam*3 = -3
print("control (9,8,-1)->C3:", search(e, add, 3, 0, 6, -3))
