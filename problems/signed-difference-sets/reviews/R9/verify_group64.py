"""SDS(64,46,30) from an NL_8(2) PDS S in an abelian group C_a1 x ... (orders on the command line):
P = G - 0 - S, D = P marked +1, 0 marked -1; checked directly on every shift (as IsSDS reads).
Usage: python verify_group64.py "<S as python list of tuples>" a1 a2 ..."""
import ast, itertools, sys
S = [tuple(x) for x in ast.literal_eval(sys.argv[1])]
ords = [int(a) for a in sys.argv[2:]]
G = list(itertools.product(*[range(o) for o in ords]))
add = lambda x, y: tuple((a + b) % o for a, b, o in zip(x, y, ords))
neg = lambda x: tuple((-a) % o for a, o in zip(x, ords))
zero = tuple(0 for _ in ords)
Sset = set(S)
assert len(Sset) == 18 and zero not in Sset and all(neg(x) in Sset for x in S)
def pds(Q):
    lam, mu = set(), set()
    for g in G:
        if g == zero: continue
        c = sum(1 for y in Q if add(y, g) in Q)
        (lam if g in Q else mu).add(c)
    return len(Q), lam, mu
P = {g for g in G if g != zero and g not in Sset}
D = {g: (1 if g in P else -1 if g == zero else 0) for g in G}
vals = {sum(D[x] * D[add(x, g)] for x in G) for g in G if g != zero}
print("group", ords, "S:", pds(Sset), "P:", pds(P), "D support", sum(1 for g in G if D[g]), "autocorrelations:", vals)
