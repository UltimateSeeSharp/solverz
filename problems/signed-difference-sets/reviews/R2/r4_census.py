"""Generic exhaustion of SDSs with exactly one negative element (moved to 0) in prod Z_f:
D = P - 0, P a (k-1)-subset of G - 0. Translation via per-chunk lookup tables (independent of
r4_c3c9_census.py's row rotation). Also reports the full signed autocorrelation of each hit.
Usage: python r4_census.py k lam f1 f2 ..."""
import itertools, sys
k, lam, f = int(sys.argv[1]), int(sys.argv[2]), [int(x) for x in sys.argv[3:]]
G = list(itertools.product(*[range(m) for m in f]))
pos = {g: i for i, g in enumerate(G)}
add = lambda u, w: tuple((a + b) % m for a, b, m in zip(u, w, f))
neg = lambda u: tuple((-a) % m for a, m in zip(u, f))
CH = 7
nch = (len(G) + CH - 1) // CH
def tables(g):
    T = []
    for c in range(nch):
        row = []
        for val in range(1 << CH):
            out = 0
            for b in range(CH):
                i = c * CH + b
                if i < len(G) and val >> b & 1: out |= 1 << pos[add(G[i], g)]
            row.append(out)
        T.append(row)
    return T
zero = G[0]
reps, seen = [], set()
for g in G[1:]:
    if g in seen: continue
    seen |= {g, neg(g)}
    reps.append((tables(g), 1 << pos[g], 1 << pos[neg(g)]))
MASK = (1 << CH) - 1
def tr(m, T):
    out = 0
    for c in range(nch): out |= T[c][(m >> (c * CH)) & MASK]
    return out
hits = []
for comb in itertools.combinations(range(1, len(G)), k - 1):
    m = 0
    for i in comb: m |= 1 << i
    for T, bg, bng in reps:
        if (m & tr(m, T)).bit_count() - ((m & bg) != 0) - ((m & bng) != 0) != lam: break
    else:
        hits.append(m)
def full_check(m):
    D = {G[i]: 1 for i in range(len(G)) if m >> i & 1}; D[zero] = -1
    return all(sum(D[x] * D.get(add(x, g), 0) for x in D) == lam for g in G[1:])
print("(%d,%d,%d) in %s, N = {0}: %d sets; full check of all: %s" % (len(G), k, lam, f, len(hits), all(full_check(m) for m in hits)))
