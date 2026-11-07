# Independent recomputation of C22's row list from instances.csv (refuter, 2026-11-06).
import csv, re, math, collections, sys
P = "problems/signed-difference-sets/"
KEY = re.compile(r"^SDS\((-?\d+),(-?\d+),(-?\d+),\[([0-9,]+)\]\)$")
INF = 10**9

def val(x, p):
    if x == 0:
        return INF
    c = 0
    x = abs(x)
    while x % p == 0:
        x //= p
        c += 1
    return c

def primes(x):
    out = []
    d = 2
    while d * d <= x:
        if x % d == 0:
            out.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        out.append(x)
    return out

def c22(v, k, lam):
    """Return list of (p, reason) where C22 (full Sylow quotient, t = v_p(v)) is violated."""
    n = k - lam
    S = k + lam * (v - 1)
    assert S == n + lam * v
    if n <= 0 or S < 0:
        return None
    s = math.isqrt(S)
    if s * s != S:
        return None  # C1 already kills
    out = []
    for p in primes(v):
        t = val(v, p)
        e = val(n, p)
        if p == 2:
            m = math.isqrt(n)
            if m * m != n:
                out.append((2, "nsq"))
                continue
            w = val(m, 2)
            if min(val(s, 2), t) != min(w, t):
                out.append((2, "eq"))
        else:
            if val(s, p) < min(t, (e + 1) // 2):
                out.append((p, "div"))
    return out

rows = []
for r in csv.DictReader(open(P + "instances.csv", newline="")):
    m = KEY.match(r["key"])
    assert m, r["key"]
    v, k, lam = int(m[1]), int(m[2]), int(m[3])
    f = [int(x) for x in m[4].split(",")]
    assert math.prod(f) == v, r["key"]
    rows.append((r["id"], v, k, lam, f, r["status"], r["source"], r["evidence"]))

hits = {}
stat = collections.Counter()
for (i, v, k, lam, f, st, src, ev) in rows:
    h = c22(v, k, lam)
    if h:
        hits[i] = h
    stat[(st, bool(h))] += 1
print("rows", len(rows))
for kk in sorted(stat):
    print(kk, stat[kk])
# group independence check: hits depend only on (v,k,lam)
byp = collections.defaultdict(set)
for (i, v, k, lam, f, st, src, ev) in rows:
    byp[(v, k, lam)].add((i, st, bool(hits.get(i))))
ex_hit = [(i, v, k, lam, f) for (i, v, k, lam, f, st, src, ev) in rows if st == "exists" and i in hits]
print("exists hit:", ex_hit)
reasons = collections.Counter()
for i, h in hits.items():
    for p, rsn in h:
        reasons[(p if p < 8 else "p>=11", rsn)] += 1
print(reasons)
# gordon source vs hits
src = collections.Counter((s.split("@")[0], st) for (i, v, k, lam, f, st, s, ev) in rows if i in hits)
print("hits by source,status:", src)
open(P + "reviews/R21/my_hits.txt", "w").write(
    "".join(f"{i} {' '.join(f'{p}{r}' for p, r in h)}\n" for i, h in hits.items()))
