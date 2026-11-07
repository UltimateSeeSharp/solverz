"""Cross-check of r4's 'no' rows for SDS(32,28,12): from each found SDS(32,20,4) D, try D +- C for every
coset C of an order-8 subgroup lying in D's zero set (character argument: works iff chi(D) = -+4 on C's annihilator)."""
import itertools, sys
sys.path.insert(0, "problems/signed-difference-sets/reviews/R6")
from verify import from_r4, from_e9, parse_key, check, WT, MS
def add(a, b, f): return tuple((x + y) % m for x, y, m in zip(a, b, f))
def subgroups(f, order):
    E = list(itertools.product(*[range(m) for m in f])); z = E[0]; out = set()
    def close(gens):
        S = {z}; fr = [z]
        while fr:
            x = fr.pop()
            for g in gens:
                y = add(x, g, f)
                if y not in S: S.add(y); fr.append(y)
        return frozenset(S)
    for r in (1, 2, 3):
        for gens in itertools.combinations(E[1:], r):
            S = close(gens)
            if len(S) == order: out.add(S)
    return out
ids = {"N127", "N128", "N129", "N130", "N132"}
d = from_r4(WT + "/scratch/r4.out", ids); d.update(from_r4(WT + "/scratch/e7.out", {"N131"}))
for i, (key, ent) in sorted(d.items()):
    v, k, lam, f = parse_key(key); D = dict(ent)
    G = list(itertools.product(*[range(m) for m in f]))
    key28 = key.replace("SDS(32,20,4,", "SDS(32,28,12,")
    hits = 0; tried = 0
    for K in subgroups(f, 8):
        for c in G:
            C = {add(c, x, f) for x in K}
            if C & set(D): continue
            for sgn in (1, -1):
                tried += 1
                E = dict(D); E.update({x: sgn for x in C})
                r = check(key28 if sgn == 1 else key.replace("SDS(32,20,4,", "SDS(32,28,0,"), list(E.items()))
                if r.endswith("OK"): hits += 1; print("  HIT", i, sgn, sorted(C)[:3], r)
    print(i, key, "cosets tried", tried, "hits", hits)
