# Lean kill set vs sc2.py: (1) sc2_all.out first-reason verdicts; (2) sc2's triple logic without
# the R2dp DP, over ALL triples (not first-return), max j only, s >= 0.
import csv, re, sys, math
from collections import Counter
PF = r"problems/signed-difference-sets"
sys.path.insert(0, PF + "/reviews/R4")
from indep import factor, selfconj, quotient_types
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
certs = {l.split()[0]: l.split() for l in open(PF + "/scratch/sc_certs.txt", encoding="utf-8")}
sc2 = {l.split()[0]: l.split(None, 3)[3].strip() for l in open(PF + "/reviews/R4/sc2_all.out", encoding="utf-8")}

def triple_lite(v, k, lam, n, s, h, p, j):
    q = p ** j; c = v // h; t = s * pow(h, -1, q) % q
    V = [x for x in range(-c, c + 1) if (x - t) % q == 0]
    if len(V) <= 1: return "R1"
    t0 = V[0]
    S1, r1 = divmod(s - h * t0, q); assert r1 == 0
    num = n + lam * c - h * t0 * t0 - 2 * t0 * q * S1
    if num % (q * q): return "R2div"
    S2 = num // (q * q)
    m = S1 // h; A = S1 - h * m; B = S2 - 2 * m * S1 + h * m * m
    if B <= 0 or B < A or (B - A) % 2: return "R2basic"
    return None

def reasons(v, k, lam, shape):
    n = k - lam
    if n <= 0: return set()
    S = n + lam * v
    if S < 0 or math.isqrt(S) ** 2 != S: return {"s-not-integer"}
    s = math.isqrt(S); out = set()
    for p, e in factor(n).items():
        j = e // 2
        if j == 0: continue
        for h, m in quotient_types(shape):
            if h == 1 or h % p == 0 or not selfconj(p, m): continue
            w = triple_lite(v, k, lam, n, s, h, p, j)
            if w: out.add(w)
    return out

rows = list(csv.DictReader(open(PF + "/instances.csv", encoding="utf-8")))
lite = {}
for r in rows:
    if r["status"] != "open": continue
    mm = KEY.fullmatch(r["key"]); v, k, lam = map(int, mm.groups()[:3])
    shape = [int(x) for x in mm.group(4).split(",")]
    rs = reasons(v, k, lam, shape)
    if rs & {"R1", "R2div", "R2basic"}: lite[r["id"]] = rs
L5 = {i for i, c in certs.items() if c[2] == "C5"}; L6 = {i for i, c in certs.items() if c[2] == "C6"}
print("sc2_all first-verdict on C5 rows", Counter(sc2[i].split()[0] for i in L5))
print("sc2_all first-verdict on C6 rows", Counter(sc2[i].split()[0] for i in L6))
print("lite kills (open)", len(lite), "C5 rows in lite with R1", sum("R1" in lite.get(i, ()) for i in L5))
print("C6 rows not in lite", sorted(L6 - set(lite), key=lambda x: int(x[1:]))[:30], len(L6 - set(lite)))
print("lite not in Lean", sorted(set(lite) - L5 - L6, key=lambda x: int(x[1:]))[:30], len(set(lite) - L5 - L6))
for i in sorted(L6 - set(lite), key=lambda x: int(x[1:]))[:10]: print(" ", certs[i], sc2[i])
for i in sorted(set(lite) - L5 - L6, key=lambda x: int(x[1:]))[:10]: print(" +", i, sc2[i], lite[i])
