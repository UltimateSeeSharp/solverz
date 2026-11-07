"""(4,4,4,1)-RDS X in abelian H of order 16 relative to K (|K|=4), and the construction
D = (H - 2X) + tK  [SDS(32,20,4)],  D' = (H - 2X) + t(H - K)  [SDS(32,28,12)]
in G of order 32 with index-2 subgroup H (t a coset rep). Verified on G directly."""
import itertools, sys
sys.path.insert(0, "problems/signed-difference-sets/reviews/R6")
from verify import check

def elems(f): return list(itertools.product(*[range(m) for m in f]))
def add(a, b, f): return tuple((x + y) % m for x, y, m in zip(a, b, f))
def neg(a, f): return tuple((-x) % m for x, m in zip(a, f))
def subgroups4(f):
    E = elems(f); z = tuple(0 for _ in f); out = set()
    for a, b in itertools.combinations(E, 2):
        S = {z}; frontier = [z]
        gens = [a, b]
        while frontier:
            x = frontier.pop()
            for g in gens:
                y = add(x, g, f)
                if y not in S: S.add(y); frontier.append(y)
        if len(S) == 4: out.add(frozenset(S))
    for a in E:
        S = {z}; x = a
        while x not in S: S.add(x); x = add(x, a, f)
        if len(S) == 4: out.add(frozenset(S))
    return out

def rds(f, K):
    E = elems(f); z = tuple(0 for _ in f)
    found = []
    for X in itertools.combinations(E, 4):
        if z not in X: continue  # translate so 0 in X
        diffs = [add(a, neg(b, f), f) for a in X for b in X if a != b]
        if len(set(diffs)) == 12 and not any(d in K for d in diffs):
            found.append(X)
            break
    return found

H16 = [(2,2,2,2), (2,2,4), (4,4), (2,8), (16,)]
res = {}
for f in H16:
    for K in subgroups4(f):
        X = rds(f, K)
        if X:
            res.setdefault(f, []).append((sorted(K), X[0]))
for f in H16:
    print(f, "RDS rel K:", [(k, x) for k, x in res.get(f, [])][:3], "count K:", len(res.get(f, [])))

# embed H into G: G given by invariant factors; H as index-2 subgroup via explicit map
# simple cases: G = C2 x H (t = (1,0..)) and G=[4,8] with H=[4,4] = {(a,2b)} t=(0,1)
def build(Gf, Hmap, t, X, K, second):
    # Hmap: H coords -> G coords (injective hom), t in G
    Hel = elems(Hf)
    ent = {}
    for h in Hel:
        ent[Hmap(h)] = -1 if h in X else 1
    Bset = K if second == "K" else [h for h in Hel if h not in K]
    for h in Bset:
        ent[add(Hmap(h), t, Gf)] = 1
    return list(ent.items())
for Hf, lst in res.items():
    K, X = lst[0]
    Gf = (2,) + Hf
    Gf_sorted = tuple(sorted(Gf))
    key20 = f"SDS(32,20,4,[{','.join(map(str, Gf))}])"
    key28 = f"SDS(32,28,12,[{','.join(map(str, Gf))}])"
    Hmap = lambda h: (0,) + h
    t = (1,) + tuple(0 for _ in Hf)
    print("G = C2 x", Hf, check(key20, build(Gf, Hmap, t, set(X), set(K), "K")))
    print("G = C2 x", Hf, check(key28, build(Gf, Hmap, t, set(X), set(K), "H-K")))

# G = C4 x C8 with H = {(a, 2b)} ~ C4 x C4, t = (0, 1) of order 8 (t^2 in H)
Hf = (4, 4); K, X = res[(4, 4)][0]
Hmap = lambda h: (h[0], 2 * h[1])
print("G = [4,8]", check("SDS(32,20,4,[4,8])", build((4, 8), Hmap, (0, 1), set(X), set(K), "K")))
print("G = [4,8]", check("SDS(32,28,12,[4,8])", build((4, 8), Hmap, (0, 1), set(X), set(K), "H-K")))
