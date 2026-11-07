# Independent recount of C21's rows from instances.csv (no ideator code imported).
import csv, re, math, sys, collections, ast
W = "problems/signed-difference-sets/"
KEY = re.compile(r"SDS\((-?\d+),(-?\d+),(-?\d+),\[([\d,\s]*)\]\)")

def factorize(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def vp(x, p):
    c = 0
    while x % p == 0: x //= p; c += 1
    return c

def selfconj(p, m):
    """exists i >= 1 with p^i = -1 mod m (m coprime to p); m = 1 counts (K = 1)."""
    if m == 1: return True
    x = p % m
    for _ in range(m + 1):
        if (x + 1) % m == 0: return True
        x = x * p % m
    return False

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def best(v, n, fs):
    """Return list of (p, e, b, j, Kfactors, c) for every prime p where the rule fires (best H per p)."""
    out = []
    if n <= 0: return out
    for p in factorize(n):
        e = vp(n, p); b = e // 2
        if b == 0: continue
        j = max(vp(m, p) for m in fs)
        if j == 0: continue
        pp = [m // p ** vp(m, p) for m in fs]          # p'-parts of the factors
        expo = math.lcm(*pp)
        bestK = None
        for mm in divisors(expo):
            if not selfconj(p, mm): continue
            K = [math.gcd(x, mm) for x in pp]
            if bestK is None or math.prod(K) > math.prod(bestK): bestK = K
        Ksz = math.prod(bestK)
        assert v % (p ** j * Ksz) == 0
        c = v // (p ** j * Ksz)
        if p ** b > 2 * c:
            out.append((p, e, b, j, tuple(x for x in bestK if x > 1), c))
    return out

rows = []
for r in csv.DictReader(open(W + "instances.csv", newline='', encoding='utf-8')):
    m = KEY.fullmatch(r['key'])
    v, k, l = int(m[1]), int(m[2]), int(m[3]); fs = [int(x) for x in m[4].split(',')]
    assert math.prod(fs) == v, r
    rows.append((r['id'], v, k, l, fs, r['status'], r['evidence']))

hits = {}
for id_, v, k, l, fs, st, ev in rows:
    h = best(v, k - l, fs)
    if h: hits[id_] = (v, k, l, fs, st, h)
print("rows", len(rows), "hits", len(hits), collections.Counter(x[4] for x in hits.values()))
print("n<=0 rows:", [(r[0], r[1], r[2], r[3]) for r in rows if r[2] - r[3] <= 0][:10])
with open(W + "reviews/R20/my_hits.txt", "w") as o:
    for id_, (v, k, l, fs, st, h) in hits.items():
        o.write(f"{id_} {v} {k} {l} {fs} {st} {h}\n")
for id_, (v, k, l, fs, st, h) in hits.items():
    if st == 'exists': print("EXISTS HIT", id_, v, k, l, fs, h)
