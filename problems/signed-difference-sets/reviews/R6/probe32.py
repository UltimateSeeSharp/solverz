"""Order-32 sets: for each index-2 subgroup H (kernel of a hom G -> Z2), the support/sign profile on H and G\H,
and whether D matches the RDS shape: one coset fully marked (16 elements, 4 or 12 minus as X), other coset
= a coset of an order-4 subgroup (k=20) or its complement in the coset (k=28)."""
import itertools, sys
sys.path.insert(0, "problems/signed-difference-sets/reviews/R6")
from verify import from_r4, from_e9, parse_key, WT, MS
def homs2(f):
    # homs G -> Z2: x -> sum c_i * x_i * (2/m_i)?? for Z_m with m even: x -> c*x mod 2 ; m odd: 0
    for cs in itertools.product(*[(0, 1) for _ in f]):
        if any(cs): yield cs
def ev(cs, x, f): return sum(c * xi for c, xi in zip(cs, x)) % 2
def is_coset_of_subgroup(S, f):
    S = list(S)
    if not S: return False
    a = S[0]
    T = {tuple((x - y) % m for x, y, m in zip(s, a, f)) for s in S}
    return all(tuple((x + y) % m for x, y, m in zip(p, q, f)) in T for p in T for q in T)
ids = {"N127", "N128", "N129", "N130", "N132", "N137", "N139"}
d = from_r4(WT + "/scratch/r4.out", ids); d.update({i + "e7": x for i, x in from_r4(WT + "/scratch/e7.out", {"N131"}).items()})
d.update({i + "e9": x for i, x in from_e9(MS + "/e8/e9-200.out", {"N130", "N132", "N139"}).items()})
for i, (key, ent) in sorted(d.items()):
    v, k, lam, f = parse_key(key); D = dict(ent)
    prof = []
    for cs in homs2(f):
        H0 = {x: s for x, s in D.items() if ev(cs, x, f) == 0}; H1 = {x: s for x, s in D.items() if ev(cs, x, f) == 1}
        a = (len(H0), sum(H0.values()), sum(1 for s in H0.values() if s < 0))
        b = (len(H1), sum(H1.values()), sum(1 for s in H1.values() if s < 0))
        rds_shape = False
        for A, B in ((a, H1), (b, H0)):
            if A[0] == 16 and len(B) in (4, 12):
                Bs = set(B) if len(B) == 4 else None
                if len(B) == 4: rds_shape = is_coset_of_subgroup(B, f) and all(s == 1 for s in B.values())
                else:
                    other = [x for x in itertools.product(*[range(m) for m in f]) if ev(cs, x, f) == (1 if B is H1 else 0) and x not in B]
                    rds_shape = is_coset_of_subgroup(other, f) and all(s == 1 for s in B.values())
        prof.append((a, b, "RDS-shape" if rds_shape else ""))
    shapes = sorted(set((p[0], p[1]) for p in prof))
    print(i, key, "RDS-shape on some H:", any(p[2] for p in prof), "| profiles (k,sum,#minus) on H, G\H:", shapes)
