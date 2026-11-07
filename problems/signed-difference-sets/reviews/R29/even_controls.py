"""Positive control for even_rows_search.search: object rows with 4 | n on small L must yield >= 1 vector."""
import sys, re, glob
from math import lcm
from functools import reduce
sys.argv = sys.argv[:1]
import importlib.util
spec = importlib.util.spec_from_file_location("ers", "even_rows_search.py")
src = open("even_rows_search.py", encoding="utf-8").read().split("for i, row in rows.items():")[0]
ns = {}; exec(src, ns); search = ns["search"]
root = "../../.."
done = 0
for path in sorted(glob.glob(root + "/objects/O*.txt")):
    hdr = re.match(r"(\S+) \((\d+),(\d+),(-?\d+)\)", open(path, encoding="utf-8").readline())
    ms = [int(x) for x in hdr.group(1).replace("C", "").split("x")]
    v, k, lam = int(hdr.group(2)), int(hdr.group(3)), int(hdr.group(4))
    if (k - lam) % 4: continue
    s = int(round(abs(k + lam * (v - 1)) ** 0.5))
    w = reduce(lcm, ms)
    for r, d in [(16, 1), (8, 1), (4, 3), (1, 9), (2, 5), (4, 1), (2, 3), (1, 5), (2, 1), (1, 3)]:
        if w % (2 * r) or w % d or v % (2 * r * d) or r * d > 16: continue
        c = v // (2 * r * d)
        if (k + lam * (2 * c - 1)) % 4 or (lam * c) % 2: continue
        K = k // 2
        if (K - s // 2) % 2: K -= 1
        Q, t, s2, sols = search(v, k, lam, r, d, c, s, K)
        print(path.split("/")[-1], (v, k, lam), "r", r, "d", d, "c", c, "solutions", len(sols), flush=True)
        done += 1
        break
    if done >= 40: break
