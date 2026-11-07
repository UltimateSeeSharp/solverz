"""Completeness: status in sds.json / instances.csv of every key the opened theorems construct, v <= VMAX."""
import csv, json, sys
from build import GF, prime_divisors

db = json.load(open(sys.argv[1]))
inst = {r["key"]: r for r in csv.DictReader(open(sys.argv[2], encoding="utf-8"))}
vmax = max(int(k[4:].split(",")[0]) for k in db)
print("max v in sds.json:", vmax)


def prime_power(v):
    ps = prime_divisors(v)
    if len(ps) != 1:
        return None
    p, e = ps[0], 0
    while v > 1:
        v //= p
        e += 1
    return p, e


def inv_factors(parts):
    """Invariant factors of prod Z_{p^a} given as a list of prime powers."""
    from collections import defaultdict
    by = defaultdict(list)
    for x in parts:
        p = prime_divisors(x)[0]
        by[p].append(x)
    for p in by:
        by[p].sort(reverse=True)
    L = max(len(l) for l in by.values())
    out = []
    for i in range(L):
        m = 1
        for l in by.values():
            if i < len(l):
                m *= l[i]
        out.append(m)
    return sorted(out)


def show(tag, v, k, lam, factors):
    key = f"SDS({v},{k},{lam},[{','.join(map(str, factors))}])"
    e = db.get(key)
    r = inst.get(key)
    st = e["status"] if e else "ABSENT"
    flag = "   <-- Open" if st == "Open" else ""
    print(f"{tag}: {key} db={st} '{e['comment'] if e else ''}' csv={r['id'] + ' ' + r['status'] if r else '-'}{flag}")


print("# Gordon Prop 2.3 (Paley and zero), v = 3 mod 4 prime power")
for v in range(3, vmax + 1, 4):
    pe = prime_power(v)
    if pe:
        p, e = pe
        n = (v + 1) // 4
        show("P2.3", v, 2 * n, n - 2, [p] * e)
print("# Gordon Thm 4.1, q, q+6 prime powers")
for m in range(3, 200):
    q, r = 2 * m - 3, 2 * m + 3
    if q * r > vmax:
        break
    a, b = prime_power(q), prime_power(r)
    if a and b:
        n = m * m
        show("T4.1", q * r, 2 * n - 1, n - 1, inv_factors([a[0]] * a[1] + [b[0]] * b[1]))
print("# Gordon Thm 3.2 (4th powers, N = {0}; v = 25 + 4y^2 prime, y odd, v = 13 mod 16)")
for y in range(1, 40, 2):
    v = 25 + 4 * y * y
    if v <= vmax and v % 16 == 13 and prime_power(v) and prime_power(v)[1] == 1:
        show("T3.2", v, (v + 3) // 4, (v - 13) // 16, [v])
print("# HCG Thm 4.1 (m even): (3^(2m+1), 3^(2m)+1, 1) in Z3^(2m+1)")
for m in (2, 4):
    v = 3 ** (2 * m + 1)
    if v <= vmax:
        show("HCG4.1", v, 3 ** (2 * m) + 1, 1, [3] * (2 * m + 1))
