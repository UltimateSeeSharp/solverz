# (a) My own rule (all primes, all j <= v_p(n)/2, all coordinatewise quotients, self-conjugacy
# as exp(H) | p^i + 1 for some i) and sc_rows.py's cert() on every row; must fire on no `exists`.
# (b) Latent: rows where sc_rows' j = max(j,1) admits a prime with v_p(n) = 1.
import csv, re, math, itertools, sys, collections
PF = sys.argv[1]
src = open(PF + "/scratch/sc_rows.py", encoding="utf-8").read().split("rows = list(")[0]
ns = {}; exec(src, ns); cert = ns["cert"]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
def pf(n):
    out, p = {}, 2; n = abs(n)
    while p * p <= n:
        while n % p == 0: out[p] = out.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out
def selfconj(p, e):  # exists i >= 1 with e | p^i + 1
    x = p % e
    for i in range(1, 2 * e + 2):
        if (x + 1) % e == 0: return i
        x = x * p % e
    return None
def divs(m): return [d for d in range(1, m + 1) if m % d == 0]
def mine(v, k, lam, ms, allow_odd=False):
    n = k - lam
    if n == 0: return None
    for p, e in pf(n).items():
        J = e // 2 if not allow_odd else max(e // 2, 1)
        if J == 0: continue
        for ds in itertools.product(*[divs(m) for m in ms]):
            h = math.prod(ds)
            if h == 1 or h % p == 0: continue
            if 2 * (v // h) >= p ** J: continue
            i = selfconj(p, math.lcm(*ds))
            if i: return (p, J, i, ds)
    return None
rows = list(csv.DictReader(open(PF + "/instances.csv", encoding="utf-8")))
st = collections.Counter(r["status"] for r in rows); print("statuses", dict(st))
fire = collections.Counter(); ex = collections.defaultdict(list); odd_only = []
for r in rows:
    m = KEY.fullmatch(r["key"]); v, k, lam = map(int, m.groups()[:3]); ms = [int(x) for x in m.group(4).split(",")]
    a = mine(v, k, lam, ms); b = cert(v, k, lam, ms)
    if a: fire["mine", r["status"]] += 1
    if b: fire["sc_rows", r["status"]] += 1
    if bool(a) != bool(b): ex["disagree"].append((r["id"], r["key"], a, b))
    if (a or b) and r["status"] == "exists": ex["EXISTS FIRED"].append((r["id"], r["key"], a, b))
    if not a and mine(v, k, lam, ms, True): odd_only.append((r["id"], r["status"], r["key"]))
print(dict(fire))
for t, l in ex.items(): print(t, len(l), l[:5])
print("rows only an e=1 prime (j forced to 1) would kill:", len(odd_only), collections.Counter(s for _, s, _ in odd_only), odd_only[:5])
