"""Which table entries SDS(v,K,L) could the lemma reach? Need a PDS (v, K-1, L+2, L) with feasible SRG
parameters: k(k-l-1) = (v-k-1)mu, integral eigenvalue multiplicities (eigenvalues 1 +- s, s^2 = k - mu + 1).
Lists distinct (v,K,L) with open entries and the number of open groups."""
import csv, re, sys
from collections import defaultdict
rows = list(csv.DictReader(open(sys.argv[1], encoding="utf-8")))
groups = defaultdict(lambda: [0, 0])
for r in rows:
    m = re.match(r"SDS\((\d+),(\d+),(-?\d+),\[(.*)\]\)", r["key"])
    v, K, L = map(int, m.group(1, 2, 3))
    g = groups[(v, K, L)]; g[0] += 1; g[1] += r["status"] == "open"
out = []
for (v, K, L), (tot, op) in sorted(groups.items()):
    k, lam, mu = K - 1, L + 2, L
    if not (0 < k < v - 1) or mu <= 0 or lam < 0: continue
    if k * (k - lam - 1) != (v - k - 1) * mu: continue
    s2 = k - mu + 1
    s = int(round(s2 ** 0.5))
    if s * s != s2: continue
    th, ta = 1 + s, 1 - s
    # multiplicities f (for th), g (for ta): f + g = v - 1, k + f th + g ta = 0
    num = -k - (v - 1) * ta
    if num % (th - ta): continue
    f = num // (th - ta); g = v - 1 - f
    if f <= 0 or g <= 0: continue
    kc, lc, mc = v - k - 1, v - 2 - 2 * k + mu, v - 2 * k + lam
    if lc < 0 or mc <= 0: continue
    # absolute bound and Krein are not checked
    n = int(round(v ** 0.5)); typ = ""
    if n * n == v:
        if k % (n + 1) == 0 and k // (n + 1) == n // 2 + 1: typ = "NL_n(n/2+1)"
        elif k % (n - 1) == 0 and k // (n - 1) == n // 2 - 1: typ = "L_n(n/2-1)"
    out.append((v, K, L, tot, op, v, k, lam, mu, typ))
for o in out: print("SDS(%d,%d,%d): %d groups, %d open; needs PDS (%d,%d,%d,%d) %s" % o)
