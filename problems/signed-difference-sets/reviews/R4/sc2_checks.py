# Validate full R2 (sc2): never kills a verified known set's parameters; never declares
# infeasible a quotient on which E8 found a contraction vector.
import sys, re, math, ctypes
ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)
sys.path.insert(0, ".")
import sc2, known_sets as K, constructions
from indep import factor, selfconj
kills = []; nsets = 0
for src in (K.gordon_sets(), K.project_sets(), constructions.all_sets()):
    for name, shape, k, lam, A in src:
        if not K.is_sds(A, k, lam): continue
        nsets += 1; w = sc2.verdict(math.prod(shape), k, lam, shape)
        if w: kills.append((name, w))
print("known sets:", nsets, "killed:", kills[:5])
KEY = sc2.KEY; tested = 0; hits = []
for l in open("../../e8/combined.out", encoding="utf-8"):
    t = l.split()
    if len(t) < 4 or t[3] != "open": continue
    v, k, lam = map(int, KEY.fullmatch(t[1]).groups()[:3]); n = k - lam; s = math.isqrt(n + lam * v)
    for item in t[4:]:
        H, flag = item.rsplit(":", 1)
        if flag != "found": continue
        fs = [int(x) for x in H.strip("[]").split(",")]; h, m = math.prod(fs), math.lcm(*fs)
        for p, e in factor(n).items():
            if e < 2 or h == 1 or h % p == 0 or not selfconj(p, m): continue
            tested += 1; why = sc2.triple(v, k, lam, n, s, h, p, e // 2)
            if why: hits.append((t[0], t[1], H, p, why))
print("E8 found-quotient triples:", tested, "declared infeasible:", len(hits), hits[:5])
