"""SDS(64,46,30) in C8 x C8 (N744): S = an NL_8(2) (64,18,2,6) PDS found by rat/ (rational-class search);
P = G - 0 - S is NL_8(5); D = P marked +1, 0 marked -1. Checked here directly on every shift, as IsSDS reads."""
S = [(0,1),(0,3),(0,5),(0,7),(1,0),(1,1),(2,4),(2,6),(3,0),(3,3),(4,2),(4,6),(5,0),(5,5),(6,2),(6,4),(7,0),(7,7)]
G = [(a, b) for a in range(8) for b in range(8)]
add = lambda x, y: ((x[0] + y[0]) % 8, (x[1] + y[1]) % 8)
Sset = set(S)
assert len(Sset) == 18 and (0, 0) not in Sset and all(((-a) % 8, (-b) % 8) in Sset for a, b in S)
def pds(Pset):
    lam, mu = set(), set()
    for g in G:
        if g == (0, 0): continue
        c = sum(1 for y in Pset if add(y, g) in Pset)
        (lam if g in Pset else mu).add(c)
    return len(Pset), lam, mu
print("S:", pds(Sset))
P = {g for g in G if g != (0, 0) and g not in Sset}
print("P:", pds(P))
D = {g: (1 if g in P else -1 if g == (0, 0) else 0) for g in G}
vals = {sum(D[x] * D[add(x, g)] for x in G) for g in G if g != (0, 0)}
print("D support", sum(1 for g in G if D[g]), "signed autocorrelations on all 63 shifts:", vals)
