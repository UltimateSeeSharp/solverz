"""Independent recomputation of C26's kills over instances.csv (no solver imports).
Quotient types: C_{2^j} (j <= largest 2-part of a factor) x K, K any quotient type of the odd part (per prime, a
partition contained in G's), 2 self-conjugate mod exp K. Kill: 4 | n > 0, S = k + lam (v - 1) a square s^2,
8 divides neither 2s - (k + lam (2c - 1)) nor -2s - (k + lam (2c - 1))."""
import csv, re, math, itertools, collections, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

def factor(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def selfconj2(m):
    if m == 1: return True
    return any(pow(2, i, m) == m - 1 for i in range(1, m + 1))

def sub_partitions(lam):
    """All partitions mu (as sorted tuples, possibly with zeros) with mu_t <= lam_t (lam sorted desc)."""
    return set(tuple(sorted(mu, reverse=True)) for mu in itertools.product(*[range(a + 1) for a in lam]))

def quotient_cs(ms):
    v = math.prod(ms)
    J = max(factor(m).get(2, 0) for m in ms)
    primes = sorted({p for m in ms for p in factor(m) if p != 2})
    parts = {p: sorted([factor(m).get(p, 0) for m in ms if factor(m).get(p, 0)], reverse=True) for p in primes}
    opts = {p: [(p ** sum(mu), p ** (mu[0] if mu else 0)) for mu in sub_partitions(parts[p])] for p in primes}
    out = set()
    for combo in itertools.product(*[opts[p] for p in primes]):
        size = math.prod(a for a, _ in combo); ex = math.prod(b for _, b in combo)
        if not selfconj2(ex): continue
        for j in range(1, J + 1):
            out.add((v // (2 ** j * size), 2 ** (j - 1)))
    return out

def killing(ms, k, lam):
    v = math.prod(ms); n = k - lam
    if n <= 0 or n % 4: return []
    S = k + lam * (v - 1)
    if S < 0 or math.isqrt(S) ** 2 != S: return []
    s = math.isqrt(S)
    res = []
    for c, r in sorted(quotient_cs(ms)):
        t = k + lam * (2 * c - 1)
        if (2 * s - t) % 8 and (-2 * s - t) % 8: res.append((c, r))
    return res

if __name__ == "__main__":
    rows = list(csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8")))
    hits = collections.defaultdict(list); detail = {}
    for row in rows:
        v, k, lam, ms = KEY.fullmatch(row["key"]).groups()
        v, k, lam = int(v), int(k), int(lam); ms = [int(x) for x in ms.split(",")]
        assert math.prod(ms) == v, row
        kl = killing(ms, k, lam)
        if kl:
            hits[row["status"]].append(row["id"]); detail[row["id"]] = (row["key"], kl)
    print({s: len(x) for s, x in hits.items()})
    out = ROOT / "reviews/R28/indep_hits.tsv"
    with open(out, "w") as f:
        for st, ids in hits.items():
            for i in ids: f.write(f"{i}\t{st}\t{detail[i][0]}\t{detail[i][1]}\n")
