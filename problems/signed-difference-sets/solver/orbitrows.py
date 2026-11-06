"""Lean row theorems for I5: E10/E11's `none` rows with squarefree n, closed by C15 and the
verified orbit search (`not_hasSDS_of_orbitRow`, `OrbitSearch.lean`); with `--non-squarefree`,
the rows with n not squarefree, closed by C9 for every n (I13, `not_hasSDS_of_orbitRow'`,
`OrbitSearchWitt.lean`), into new parts only (an existing part file is never overwritten).

`orbitrows.py <min leaves> <max leaves> <rows per part> <first part> [--non-squarefree]`: reads instances.csv (open rows), scratch/e10.out and
scratch/e11.out (`none` rows); t is a generator of C9's multiplier group (as `orbits.rs`), s the
sign sum (C1); rows are ordered by the count-pruned search size (leaves: sign choices the Lean
search evaluates) and written to lean/SignedDifferenceSets/OrbitRows/Part<NN>.lean, one theorem per
row. Standard library only; Lean rechecks every condition.
"""
import csv
import math
import re
import sys
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT_DIR = ROOT / "lean" / "SignedDifferenceSets" / "OrbitRows"
RUNS = [ROOT / "scratch" / "e10.out", ROOT / "scratch" / "e11.out"]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
OPEN, NONE = "open", "none"
NON_SQUAREFREE = "--non-squarefree"


def prime_divisors(n):
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def squarefree(n):
    return all(n % (p * p) for p in prime_divisors(n))


def generator(shape, n):
    """A generator of M = ⋂_{p | n} ⟨p mod e⟩ (cyclic, inside ⟨p₁⟩)."""
    e = math.lcm(*shape)
    def powers(p):
        out, x = [1 % e], p % e
        while x != 1 % e:
            out.append(x)
            x = x * p % e
        return out
    ps = prime_divisors(n)
    first = powers(ps[0])
    mem = set(first)
    for p in ps[1:]:
        mem &= set(powers(p))
    return first[len(first) // len(mem) % len(first)]


def orbit_sizes(shape, t):
    v = math.prod(shape)
    def scale(x):
        out, place = 0, 1
        for m in reversed(shape):
            out += (x % m) * (t % m) % m * place
            place *= m
            x //= m
        return out
    seen, sizes = [False] * v, []
    for x in range(v):
        if seen[x]:
            continue
        size, y = 0, x
        while not seen[y]:
            seen[y] = True
            size += 1
            y = scale(y)
        sizes.append(size)
    return sizes


def leaves(sizes, plus, minus):
    """Sign choices with exactly `plus` + and `minus` − elements (the Lean search's leaves)."""
    @lru_cache(None)
    def go(d, p, m):
        if d == len(sizes):
            return 1 if (p, m) == (plus, minus) else 0
        c = sizes[d]
        return sum(go(d + 1, p2, m2) for p2, m2 in ((p + c, m), (p, m + c), (p, m))
                   if p2 <= plus and m2 <= minus)
    return go(0, 0, 0)


def rows(min_leaves, max_leaves, non_squarefree=False):
    status = {r["id"]: r["status"] for r in csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8"))}
    out = []
    for run in RUNS:
        for line in open(run, encoding="utf-8"):
            f = line.split()
            if len(f) < 3 or f[2] != NONE or status.get(f[0]) != OPEN:
                continue
            m = KEY.fullmatch(f[1])
            v, k, lam = map(int, m.groups()[:3])
            shape = [int(x) for x in m.group(4).split(",")]
            n = k - lam
            if n <= 1 or squarefree(n) == non_squarefree or math.gcd(v, n) != 1:
                continue
            s = math.isqrt(k + lam * (v - 1))
            t = generator(shape, n)
            sizes = orbit_sizes(shape, t)
            lv = leaves(tuple(sizes), (k + s) // 2, (k - s) // 2)
            if min_leaves <= lv <= max_leaves:
                out.append((lv, len(sizes), f[0], shape, k, lam, t, s))
    out.sort()
    return out


def write(rs, per_part, first=1, non_squarefree=False):
    OUT_DIR.mkdir(exist_ok=True)
    if non_squarefree:
        lemma, module, n_kind, by = ("not_hasSDS_of_orbitRow'", "OrbitSearchWitt", "n not squarefree",
                                     "C9 for every n (I13)")
        taken = [first + i // per_part for i in range(0, len(rs), per_part)
                 if (OUT_DIR / f"Part{first + i // per_part:02d}.lean").exists()]
        if taken:
            sys.exit(f"parts {taken} exist; choose another first part")
    else:
        lemma, module, n_kind, by = "not_hasSDS_of_orbitRow", "OrbitSearch", "squarefree n", "C15"
    for idx in range(0, len(rs), per_part):
        part, num = rs[idx: idx + per_part], first + idx // per_part
        body = []
        for lv, r, nid, shape, k, lam, t, s in part:
            grp = " × ".join(f"ZMod {m}" for m in shape)
            lam_lean = f"({lam})" if lam < 0 else str(lam)
            body.append(f"""/-- {nid}: {r} orbits of x ↦ {t}x, {lv} sign choices to evaluate. -/
theorem {nid.lower()}_not_hasSDS : ¬ HasSDS ({grp}) {k} {lam_lean} :=
  {lemma} (ms := [{', '.join(map(str, shape))}]) (t := {t}) (s := {s})
    (by decide +kernel) _
""")
        text = f"""module

public import SignedDifferenceSets.{module}

/-!
# Rows killed by {by} and the orbit search, part {num:02d}

{len(part)} open rows ({part[0][2]} to {part[-1][2]} in search order) with {n_kind}, coprime
to v, that E10/E11 exhausted; each closed by `{lemma}` (generated by
`solver/orbitrows.py`).
-/

@[expose] public section

namespace SignedDifferenceSets.OrbitRows

set_option maxRecDepth 100000

{chr(10).join(body)}
end SignedDifferenceSets.OrbitRows
"""
        (OUT_DIR / f"Part{num:02d}.lean").write_text(text, encoding="utf-8", newline="\n")
    print(f"{len(rs)} rows in {(len(rs) + per_part - 1) // per_part} parts")


if __name__ == "__main__":
    nsq = NON_SQUAREFREE in sys.argv[1:]
    args = [a for a in sys.argv[1:] if a != NON_SQUAREFREE]
    write(rows(int(args[0]), int(args[1]), nsq), int(args[2]), int(args[3]), nsq)
