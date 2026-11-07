# Check every line of ma_hits.txt: row data matches instances.csv and its (p, j, K) witness meets C21's hypotheses.
import csv, re, math, ast, collections
W = "problems/signed-difference-sets/"
KEY = re.compile(r"SDS\((-?\d+),(-?\d+),(-?\d+),\[([\d,\s]*)\]\)")
R = {}
for r in csv.DictReader(open(W + "instances.csv", newline='', encoding='utf-8')):
    m = KEY.fullmatch(r['key']); R[r['id']] = (int(m[1]), int(m[2]), int(m[3]), [int(x) for x in m[4].split(',')])
def vp(x, p):
    c = 0
    while x % p == 0: x //= p; c += 1
    return c
def isprime(p): return p > 1 and all(p % d for d in range(2, int(p ** .5) + 1))
def sc(p, m):
    if m == 1: return True
    return any((pow(p, i, m) + 1) % m == 0 for i in range(1, m + 1))
def primary(fs):  # multiset of prime powers
    out = collections.defaultdict(list)
    for m in fs:
        x = m; q = 2
        while x > 1:
            if x % q == 0:
                a = vp(x, q); out[q].append(a); x //= q ** a
            q += 1
    return {q: sorted(v, reverse=True) for q, v in out.items()}
def is_quotient(Kf, fs, p):
    """K (list of cyclic orders) is a quotient of the p'-part of G: per prime q, sorted exponents dominated."""
    GK, KK = primary(fs), primary(Kf)
    for q, ks in KK.items():
        if q == p: return False
        gs = GK.get(q, [])
        if len(ks) > len(gs) or any(a > g for a, g in zip(ks, gs)): return False
    return True
bad = []; cnt = collections.Counter(); minmargin = []
for l in open(W + "scratch/ideator/r2/ma_hits.txt"):
    head, rest = l.split('[', 1)
    id_, v, k, lam = head.split(); v, k, lam = int(v), int(k), int(lam)
    fs_s, tail = rest.split(']', 1)
    fs = [int(x) for x in fs_s.split(',')]
    t = tail.split(None, 2); p, j = int(t[0]), int(t[1]); Kf = list(ast.literal_eval(t[2]))
    V, K_, L, F = R[id_]
    ok = (V, K_, L, F) == (v, k, lam, fs)
    n = k - lam; e = vp(n, p); b = e // 2
    Kf = [x for x in Kf if x > 1]; Ks = math.prod(Kf); expK = math.lcm(*Kf) if Kf else 1
    ok &= isprime(p) and n > 0 and e >= 2 and j >= 1 and max(vp(m, p) for m in fs) >= j
    ok &= all(x % p for x in Kf) and is_quotient(Kf, fs, p) and sc(p, expK)
    ok &= v % (p ** j * Ks) == 0
    c = v // (p ** j * Ks); ok &= p ** b > 2 * c
    if not ok: bad.append(l.strip())
    cnt[(p, 'K=1' if Ks == 1 else 'K>1')] += 1
    minmargin.append((p ** b / (2 * c), id_))
print("bad", len(bad), bad[:5]); print(sorted(cnt.items()))
minmargin.sort(); print("tightest p^b/(2c):", minmargin[:5])
