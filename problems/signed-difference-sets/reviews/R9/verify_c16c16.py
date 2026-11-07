"""SDS(256,106,42) in C16 x C16 via the lemma: P = an L_16(7) (256,105,44,42) PDS found by rat (rat/L256_16_16.out,
first hit); D = P marked +1, 0 marked -1. Direct check on every shift."""
import ast, sys
line = next(l for l in open(sys.argv[1]) if l.startswith("HIT"))
P = {tuple(x) for x in ast.literal_eval(line.split(": ", 1)[1])}
N = 16
G = [(a, b) for a in range(N) for b in range(N)]
add = lambda x, y: ((x[0] + y[0]) % N, (x[1] + y[1]) % N)
assert (0, 0) not in P and all(((-a) % N, (-b) % N) in P for a, b in P)
lam, mu = set(), set()
for g in G:
    if g == (0, 0): continue
    c = sum(1 for y in P if add(y, g) in P)
    (lam if g in P else mu).add(c)
print("P:", len(P), "lambda", lam, "mu", mu)
D = {g: (1 if g in P else -1 if g == (0, 0) else 0) for g in G}
vals = {sum(D[x] * D[add(x, g)] for x in G) for g in G if g != (0, 0)}
print("D support", sum(1 for g in G if D[g]), "autocorrelations on all 255 shifts:", vals)
print("P =", sorted(P))
