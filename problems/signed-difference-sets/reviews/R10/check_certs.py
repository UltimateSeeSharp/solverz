# Independent check: every line of sc_rows.txt meets the hypotheses of
# SignedDifferenceSets.not_hasSDS_of_selfConj for G = prod ZMod m_i, H = prod ZMod d_i.
import csv, re, math, sys, collections
PF = sys.argv[1]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
def isprime(p): return p > 1 and all(p % q for q in range(2, int(p**.5) + 1))
def vp(n, p):
    n, e = abs(n), 0
    while n % p == 0: n //= p; e += 1
    return e
rows = {r["id"]: r for r in csv.DictReader(open(PF + "/instances.csv", encoding="utf-8"))}
bad = collections.Counter(); ids = []; examples = collections.defaultdict(list)
def fail(tag, line):
    bad[tag] += 1
    if len(examples[tag]) < 5: examples[tag].append(line.strip())
for line in open(PF + "/scratch/sc_rows.txt", encoding="utf-8"):
    rid, key, p, j, i, ds = line.split()
    p, j, i = int(p), int(j), int(i); ds = [int(x) for x in ds.split(",")]
    ids.append(rid)
    r = rows[rid]
    if r["key"] != key: fail("key mismatch", line)
    if r["status"] != "open": fail("not open", line)
    v, k, lam, ms = KEY.fullmatch(key).groups(); v, k, lam = int(v), int(k), int(lam)
    ms = [int(x) for x in ms.split(",")]
    n = k - lam
    if math.prod(ms) != v: fail("prod m != v", line)
    if len(ds) != len(ms) or any(m % d for d, m in zip(ds, ms)): fail("d !| m", line)
    h = math.prod(ds); c = v // h
    if v != c * h: fail("card", line)
    if not isprime(p): fail("p not prime", line)
    if i < 1: fail("i<1", line)
    if any((p**i + 1) % d for d in ds): fail("not selfconj", line)
    if h <= 1: fail("H trivial", line)
    if h % p == 0: fail("p | |H|", line)
    if n == 0: fail("n = 0", line)
    if n % p**(2*j): fail("p^(2j) !| n", line)
    if not 2 * c < p**j: fail("2c >= p^j", line)
    if n < 0: fail("n<0 (note)", line)
    if vp(n, p) % 2: fail("v_p(n) odd (note)", line)
print("lines", len(ids), "distinct", len(set(ids)))
for t, cnt in bad.items(): print(t, cnt, examples[t])
old = {l.split()[0] for l in open(PF + "/reviews/R4/kills_indep.txt") if l.split()[1] == "open"}
s = set(ids)
print("old open kills", len(old), "new", len(s), "old-new", sorted(old - s)[:10], len(old - s), "new-old", sorted(s - old)[:10], len(s - old))
