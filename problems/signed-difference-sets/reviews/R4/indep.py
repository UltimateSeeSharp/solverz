# Independent reimplementation of rule SC. Quotient types from the primary decomposition
# (all partitions mu <= lambda per prime), self-conjugacy via ord_m(p) and p^(ord/2) = -1.
import csv, re, sys, math, itertools, collections
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

def factor(n):
    f, q = {}, 2
    while q * q <= n:
        while n % q == 0:
            f[q] = f.get(q, 0) + 1; n //= q
        q += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def selfconj(p, m):
    if m <= 2: return True
    if math.gcd(p, m) != 1: return False
    t, x = 1, p % m
    while x != 1: x = x * p % m; t += 1
    return t % 2 == 0 and pow(p, t // 2, m) == m - 1

def subpartitions(lam):
    # all mu with mu_i <= lam_i (lam sorted desc), as tuples
    return itertools.product(*[range(l + 1) for l in lam])

def quotient_types(shape):
    # isomorphism types of quotients of prod Z_{m_i}: per prime q, a sub-partition of the
    # q-exponent partition. Return set of (order, exponent).
    per = collections.defaultdict(list)
    for m in shape:
        for q, e in factor(m).items(): per[q].append(e)
    choices = []
    for q, lam in per.items():
        opts = set()
        for mu in subpartitions(sorted(lam, reverse=True)):
            opts.add((q ** sum(mu), q ** max(mu) if mu else 1))
        choices.append(sorted(opts))
    out = set()
    for combo in itertools.product(*choices):
        out.add((math.prod(o for o, _ in combo), math.prod(x for _, x in combo)))
    return out

def witnesses(v, k, lam, shape):
    n = k - lam
    if n <= 0: return []
    W = []
    Q = quotient_types(shape)
    for p, e in factor(n).items():
        j = e // 2
        if j == 0: continue
        for h, m in Q:
            if h == 1 or h % p == 0: continue
            if selfconj(p, m) and p ** j > 2 * (v // h): W.append((p, j, h, m))
    return W

if __name__ == "__main__":
    rows = list(csv.DictReader(open(sys.argv[1], encoding="utf-8")))
    kills = {}
    bad = []
    for r in rows:
        mm = KEY.fullmatch(r["key"]); v, k, lam = map(int, mm.groups()[:3])
        shape = [int(x) for x in mm.group(4).split(",")]
        assert math.prod(shape) == v, r["key"]
        assert all(shape[i + 1] % shape[i] == 0 for i in range(len(shape) - 1)), r["key"]
        w = witnesses(v, k, lam, shape)
        if not w: continue
        if r["status"] == "exists": bad.append(r["id"])
        kills[r["id"]] = (r["status"], r["key"], w)
    st = collections.Counter(s for s, _, _ in kills.values())
    print("kills by status:", dict(st), "| existing killed:", bad)
    with open(sys.argv[2], "w") as f:
        for i, (s, key, w) in kills.items():
            f.write(f"{i} {s} {key} " + " ".join(f"p{p}j{j}h{h}m{m}" for p, j, h, m in w) + "\n")
