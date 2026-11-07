# Every `exists` row (and every row with status other than open/none) with 3-rank >= 1: C20 must fire at no a.
import re, csv, math, collections
from pathlib import Path
from kill20 import kills
PF = Path(__file__).resolve().parents[3]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
st = collections.Counter(); fired = []; tested = 0; allkill = collections.Counter()
for r in csv.DictReader(open(PF / "instances.csv", encoding="utf-8")):
    st[r["status"]] += 1
    m = KEY.fullmatch(r["key"]); v, k, lam = map(int, m.groups()[:3]); ms = [int(x) for x in m.group(4).split(",")]
    S = k + lam * (v - 1)
    if S < 0 or math.isqrt(S) ** 2 != S: continue
    s = math.isqrt(S); c3 = sum(1 for x in ms if x % 3 == 0)
    for a in range(1, c3 + 1):
        if 3 ** a > 3 ** 6: break
        if r["status"] == "exists": tested += 1
        if kills(3 ** a, s, k - lam):
            allkill[r["status"]] += 1
            if r["status"] == "exists": fired.append((r["id"], r["key"], a))
            break
print("statuses", dict(st)); print("exists (row,a) pairs tested", tested, "fired on exists:", fired)
print("rows killed by status:", dict(allkill))
