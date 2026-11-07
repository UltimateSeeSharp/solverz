# R1/R2 per quotient vs E8 "found" flags (a contraction vector exists there): any hit = R1/R2 wrong.
import sys, re, math
sys.path.insert(0, ".")
from indep import factor, selfconj
from refined import feasible_counts
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
hits, tested = [], 0
for l in open(sys.argv[1], encoding="utf-8"):
    t = l.split()
    if len(t) < 4 or t[3] != "open": continue
    v, k, lam = map(int, KEY.fullmatch(t[1]).groups()[:3]); n = k - lam; s = math.isqrt(n + lam * v)
    for item in t[4:]:
        H, flag = item.rsplit(":", 1)
        if flag != "found": continue
        fs = [int(x) for x in H.strip("[]").split(",")]; h, m = math.prod(fs), math.lcm(*fs); c = v // h
        for p, e in factor(n).items():
            if e < 2 or h == 1 or h % p == 0 or not selfconj(p, m): continue
            q = p ** (e // 2); tt = s * pow(h, -1, q) % q
            vals = [x for x in range(-c, c + 1) if (x - tt) % q == 0]; tested += 1
            if len(vals) <= 1 or (len(vals) <= 6 and not feasible_counts(tuple(vals), h, s, n + lam * c)):
                hits.append((t[0], t[1], H, p))
print("found-quotients with a qualifying p:", tested, "| R1/R2 would kill:", len(hits), hits[:5])
