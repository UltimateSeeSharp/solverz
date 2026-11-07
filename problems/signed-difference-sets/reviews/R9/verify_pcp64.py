"""Lemma applied to Latin-square type: H x H with |H| = 8 has the PCP {H x 0, 0 x H, diagonal}, an L_8(3)
PDS (64,21,8,6) with lambda - mu = 2, so D = P - {0} should be SDS(64,22,6). Checked directly in
C8 x C8, (C2 x C4)^2 and C2^6 (He-Wu's case, control)."""
import itertools
def check(H):
    ords = H + H
    G = list(itertools.product(*[range(o) for o in ords]))
    zero = tuple(0 for _ in ords)
    add = lambda x, y: tuple((a + b) % o for a, b, o in zip(x, y, ords))
    h = len(H)
    Hel = list(itertools.product(*[range(o) for o in H]))
    A = {tuple(x) + tuple(0 for _ in H) for x in Hel}
    B = {tuple(0 for _ in H) + tuple(x) for x in Hel}
    C = {tuple(x) + tuple(x) for x in Hel}
    assert len(A & B) == len(A & C) == len(B & C) == 1
    P = (A | B | C) - {zero}
    lam, mu = set(), set()
    for g in G:
        if g == zero: continue
        c = sum(1 for y in P if add(y, g) in P)
        (lam if g in P else mu).add(c)
    D = {g: (1 if g in P else -1 if g == zero else 0) for g in G}
    vals = {sum(D[x] * D[add(x, g)] for x in G) for g in G if g != zero}
    print("G = H x H, H =", H, "| P:", len(P), lam, mu, "| D support", sum(1 for g in G if D[g]), "autocorr", vals)
for H in ([8], [2, 4], [2, 2, 2]):
    check(H)
