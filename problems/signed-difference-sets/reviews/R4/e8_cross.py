# Cross-check: E8 reports quotients H with an integer contraction vector ("found"). Rule SC says
# no vector exists on any H meeting its condition. Any overlap is a contradiction.
import sys, re, math, collections
sys.path.insert(0, ".")
from indep import factor, selfconj
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
conf, nfound, nsat, nkill_on_sat = [], 0, 0, 0
lines = [l.split() for l in open(sys.argv[1], encoding="utf-8") if l.strip()]
for t in lines:
    v, k, lam = map(int, KEY.fullmatch(t[1]).groups()[:3]); n = k - lam
    if t[3] != "open": continue
    for item in t[4:]:
        H, flag = item.rsplit(":", 1)
        fs = [int(x) for x in H.strip("[]").split(",")]
        h, m = math.prod(fs), math.lcm(*fs)
        for p, e in factor(n).items():
            if e < 2 or h == 1 or h % p == 0 or not selfconj(p, m): continue
            if p ** (e // 2) > 2 * (v // h):
                nsat += 1
                if flag == "found": conf.append((t[0], t[1], H, p, e // 2))
    nfound += sum(x.endswith(":found") for x in t[4:])
print("E8 found-quotients:", nfound, "| (instance, H) pairs meeting the rule:", nsat, "| found among them:", len(conf), conf[:10])
# E8 KILL lines: which quotient killed, and does the rule also kill there?
kl = [t for t in lines if t[3] == "KILL"]
print("E8 KILL lines:", len(kl))
