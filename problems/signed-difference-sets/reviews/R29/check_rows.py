"""Independent recheck of UnramifiedRows.lean (C27): parse rows, match instances.csv, re-evaluate Kills
literally (Lean semantics) and mathematically (multiplier group via sympy-free code), and scan exists rows."""
import csv, re, sys
from math import gcd, prod
from functools import reduce

ROOT = sys.argv[1]
lean = open(ROOT + "/lean/SignedDifferenceSets/UnramifiedRows.lean", encoding="utf-8").read()
ROW = re.compile(r"\(⟨(\d+), \[([\d, ]+)\], (\d+), (-?\d+)⟩, ⟨(\d+), (\d+), \[([\d, ]*)\], \[([\d, ]*)\]⟩\)")
rows = [(int(a), [int(x) for x in b.split(",")], int(c), int(d), int(e), int(f),
         [int(x) for x in g.split(",")] if g.strip() else [], [int(x) for x in h.split(",")] if h.strip() else [])
        for a, b, c, d, e, f, g, h in ROW.findall(lean)]
print("rows parsed", len(rows), "distinct ids", len({r[0] for r in rows}))
# chunk sizes / names
print("chunks", re.findall(r"def (unramifiedRows\d+)", lean))

inst = {}
for r in csv.DictReader(open(ROOT + "/instances.csv", encoding="utf-8")):
    inst[r["id"]] = r
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

def factor(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def totient(m):
    r = m
    for p in factor(m): r = r // p * (p - 1)
    return r

def is_prime_lean(p):  # p in range(n+1), 2<=p, no q in [2,p) with p%q==0
    return p >= 2 and all(p % q != 0 for q in range(2, p))

def kills_lean(ms, k, lam, m, F, A, P):
    n = k - lam
    if not all(x > 0 for x in ms): return "ms"
    if not m > 1: return "m"
    if prod(ms) % m: return "m|v"
    # MapOk ms [m] [A]: FormOk m A ms: m | A_i * ms_i, A.headD 0
    Ai = lambda i: A[i] if i < len(A) else 0
    Pi = lambda i: P[i] if i < len(P) else 0
    if not all((Ai(i) * ms[i]) % m == 0 for i in range(len(ms))): return "MapOk"
    # SurjCert: dotL ms A P % m == 1 % m
    if sum(Ai(i) * Pi(i) for i in range(len(ms))) % m != 1 % m: return "Surj"
    if m % F: return "F|m"
    if not n > 0: return "n>0"
    if gcd(m, n) != 1: return "coprime"
    for u in range(m // F):
        t = 1 + F * u
        if gcd(t, m) != 1: return "tunit"
        for p in range(n + 1):
            if p >= 2 and n % p == 0 and is_prime_lean(p) if p < 5000 else (p >= 2 and n % p == 0 and len(factor(p)) == 1 and factor(p).get(p) == 1):
                if not any(t % m == pow(p, e, m) for e in range(m)): return f"mult u={u} p={p}"
    c = prod(ms) // m
    if not m * F * c * c < totient(m) * n: return "bound"
    return True

# independent math check: subgroup <p> mod m for each p | n, intersection must contain 1 + F Z
def gen_sub(p, m):
    s, x = set(), 1 % m
    while x not in s:
        s.add(x); x = x * p % m
    return s

def kills_math(v, ms, k, lam, m, F):
    n = k - lam
    if n <= 0 or gcd(m, n) != 1 or m % F or m < 2: return False
    # quotient ZMod m exists iff m | exponent of G
    from math import lcm
    if reduce(lcm, ms) % m: return False
    M = None
    for p in factor(n):
        S = gen_sub(p, m)
        M = S if M is None else M & S
    if M is None: M = set(range(m))
    if not all(((1 + F * u) % m) in M for u in range(m // F)): return False
    return totient(m) * n > m * F * (v // m) ** 2

bad = 0
for (i, ms, k, lam, m, F, A, P) in rows:
    r = inst.get(f"N{i}")
    v, kk, ll, mss = KEY.fullmatch(r["key"]).groups()
    v, kk, ll, mss = int(v), int(kk), int(ll), [int(x) for x in mss.split(",")]
    issues = []
    if (kk, ll, mss) != (k, lam, ms) or v != prod(ms): issues.append(f"key {r['key']}")
    if r["status"] != "open": issues.append("status " + r["status"])
    kl = kills_lean(ms, k, lam, m, F, A, P)
    if kl is not True: issues.append("lean-kills fails: " + kl)
    if not kills_math(v, ms, k, lam, m, F): issues.append("math fails")
    if issues:
        bad += 1; print(i, issues)
print("rows with issues:", bad)
