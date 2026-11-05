"""Write instances.csv from Gordon's signed difference set table and He-Wu's obstructions.

Source: dmgordo/signed-difference-sets `sds.json` at e3bf810 (2026-04-24), one key
SDS(v,k,lambda,[invariant factors]) per group-specific case. Yes/All -> exists, No -> none.
Open -> exists for He-Wu's three constructions (arXiv 2608.22936, Section 5) and for cases
of Gordon's paper (arXiv 2212.10630) that his database leaves Open; none when one
of their four obstructions (Theorems 3.2, 4.2, 4.4, 4.7, applied cumulatively as in their
count_open_cases.py) rules it out; else open.
IDs stay with their keys across reruns; rows we settled (settle.py) are kept as they are,
except that a literature construction takes the credit.
Run from the problem folder: python -I solver/import/import.py [path to sds.json]
"""

import csv
import json
import math
import sys
from pathlib import Path

PROBLEM = Path(__file__).resolve().parents[2]
SOURCE = Path(sys.argv[1]) if len(sys.argv) > 1 else PROBLEM / "scratch/data/gordon/sds.json"
SNAPSHOT = "e3bf810"
OUT = PROBLEM / "instances.csv"
HEADER = ["id", "key", "source", "status", "evidence", "lean", "result"]
SOURCE_STATUS = {"Yes": "exists", "All": "exists", "No": "none"}
REFERENCE_PREFIXES = ("Gordon:", "He-Wu ")
HE_WU_V_RANGE = range(9, 500)
CONSTRUCTIONS = {  # Open in the database, constructed in the literature
    # He-Wu Section 5
    "SDS(64,22,6,[2,2,2,2,2,2])": "He-Wu construction: PCP-type partial difference set",
    "SDS(256,106,42,[2,2,2,2,2,2,2,2])": "He-Wu construction: PCP-type partial difference set",
    "SDS(125,28,3,[5,5,5])": "He-Wu construction: quartic characters",
    # Gordon's paper; the database applies Prop 2.3 to prime v only and files Thm 4.1 at
    # q = 3 under [3,9]
    "SDS(27,14,5,[3,3,3])": "Gordon: paper Prop 2.3 (Paley and zero in GF(27))",
    "SDS(27,17,8,[3,3,3])": "Gordon: paper Thm 4.1 (prime power pair q = 3, GF(3) + GF(9))",
}


def parse(key):
    head, group = key[4:-2].split(",[")
    v, k, lam = (int(x) for x in head.split(","))
    factors = tuple(int(x) for x in group.split(","))
    assert math.prod(factors) == v, key
    return v, k, lam, factors


def prime_factors(n):
    out, p = [], 2
    while p * p <= n:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e:
            out.append((p, e))
        p += 1
    if n > 1:
        out.append((n, 1))
    return out


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def minus_one_power(p, m):
    """Some j >= 1 with p^j = -1 mod m, or None."""
    if math.gcd(p, m) != 1:
        return None
    r, seen, j = 1, {1}, 0
    while True:
        j += 1
        r = r * p % m
        if r == (m - 1) % m:
            return j
        if r in seen:
            return None
        seen.add(r)


def he_wu(v, k, lam, factors):
    """The first He-Wu obstruction that rules the case out, with its witness, or None."""
    n = k - lam
    if n > 0:
        exponent = math.lcm(*factors)
        for p, e in prime_factors(n):
            if e % 2:
                for m in divisors(exponent)[1:]:
                    j = minus_one_power(p, m)
                    if j is not None:
                        return f"He-Wu Thm 3.2: n={n}; p={p}; m={m}; j={j}"
    if v % 2 == 0 and n >= 0 and math.isqrt(n) ** 2 != n:
        return f"He-Wu Thm 4.2: v even; n={n} not a square"
    if k == v - 1:
        for h in divisors(v):
            if 1 < h < v and h % 2:
                q = v // h
                if (v - 1 + lam * (h - 1)) % 8 not in {(q - 1) % 8, (q + 3) % 8}:
                    return f"He-Wu Thm 4.4: h={h}; q={q}"
    p, m = factors[0], len(factors)
    if p > 2 and all(f == p for f in factors) and len(prime_factors(p)) == 1 and prime_factors(p)[0][1] == 1:
        d = v - k
        if 1 <= d <= m:
            lhs = (k + lam * (p ** (m - 1) - 1)) % 8
            allowed = {p % 8} if d % 2 == 0 else {(p - 1) % 8, (p + 3) % 8}
            if lhs not in allowed:
                return f"He-Wu Thm 4.7: p={p}; m={m}; d={d}"
    return None


def main():
    table = json.loads(SOURCE.read_text(encoding="utf-8"))
    old = {}
    if OUT.exists():
        with OUT.open(encoding="utf-8", newline="") as f:
            old = {row["key"]: row for row in csv.DictReader(f)}
    next_id = 1 + max((int(r["id"][1:]) for r in old.values()), default=0)
    rows = []
    for key in sorted(table, key=parse):
        status = table[key]["status"]
        v, k, lam, factors = parse(key)
        row = old.get(key)
        if row is None:
            row = {h: "" for h in HEADER}
            row["id"], row["key"] = f"N{next_id}", key
            next_id += 1
        row["source"] = f"{status}@{SNAPSHOT}"
        ours = row["evidence"] and not row["evidence"].startswith(REFERENCE_PREFIXES)
        if key in CONSTRUCTIONS:
            # The literature had it first, even where we found a set too (our Lean check stays).
            row["status"], row["evidence"] = "exists", CONSTRUCTIONS[key]
        elif not ours:
            if status in SOURCE_STATUS:
                comment = table[key].get("comment", "") or "table"
                row["status"], row["evidence"] = SOURCE_STATUS[status], f"Gordon: {comment}"
            else:
                witness = he_wu(v, k, lam, factors) if v in HE_WU_V_RANGE else None
                row["status"], row["evidence"] = ("none", witness) if witness else ("open", "")
        rows.append(row)
    with OUT.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, HEADER, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    counts = {}
    for r in rows:
        tag = r["status"] + (" (He-Wu)" if r["evidence"].startswith("He-Wu") else "")
        counts[tag] = counts.get(tag, 0) + 1
    print(f"wrote {OUT}: {len(rows)} Instances; {counts}")


if __name__ == "__main__":
    main()
