"""Structure probes: is D (after translation) P - e or P + e with P a regular PDS? subgroup/coset content."""
import itertools, sys
sys.path.insert(0, "problems/signed-difference-sets/reviews/R6")
from verify import from_r4, from_e9, parse_key, WT, MS

def add(a, b, f): return tuple((x + y) % m for x, y, m in zip(a, b, f))
def neg(a, f): return tuple((-x) % m for x, m in zip(a, f))
def is_pds(S, f):
    G = list(itertools.product(*[range(m) for m in f])); z = G[0]
    S = set(S)
    if z in S or any(neg(x, f) not in S for x in S): return None
    cnt = {}
    for g in G:
        if g == z: continue
        c = sum(1 for x in S if add(x, g, f) in S)
        cnt.setdefault(g in S, set()).add(c)
    if all(len(v) == 1 for v in cnt.values()):
        return (len(S), next(iter(cnt.get(True, {None}))), next(iter(cnt.get(False, {None}))))
    return None

def probe(i, key, ent):
    v, k, lam, f = parse_key(key)
    D = dict(ent)
    out = []
    for c in D:  # translate c to 0
        Dc = {add(x, neg(c, f), f): s for x, s in D.items()}
        z = tuple(0 for _ in f)
        P = [x for x, s in Dc.items() if s == 1 and x != z]
        N = [x for x, s in Dc.items() if s == -1 and x != z]
        supp = [x for x in Dc if x != z]
        r = is_pds(supp, f)
        if r: out.append((c, D[c], "support\0 PDS (k,lam,mu)=" + str(r), "minus\0:", len(N), "plus\0:", len(P)))
    return out

if __name__ == "__main__":
    r4 = from_r4(WT + "/scratch/r4.out", {"N169", "N170"})
    e9 = from_e9(MS + "/e8/e9-200.out", {"N169", "N170"})
    for src, d in [("r4", r4), ("e9", e9)]:
        for i, (key, ent) in d.items():
            res = probe(i, key, ent)
            print(src, i, key, res[:4] if res else "no translate makes support\{0} a PDS")
