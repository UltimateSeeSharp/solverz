"""Certificates for C5 and C6 (arithmetic part) on the open rows, written as Lean chunks.

`selfconj.py certs <out.txt>`: one line per open row of instances.csv that a certificate
kills: `id key rule p j i d1,...,dr s` (C5: 2c < p^j; C13: the moments test fails;
C14: the moments test or the box bound fails).
`selfconj.py lean <certs.txt> <rows per part> [first part number]`: writes the C5/C13 rows to
lean/SignedDifferenceSets/SelfConjugacyRows/Part<NN>.lean and the C14 rows to
BoxRows/Part<NN>.lean, each checked by `decide +kernel`.
Standard library only; the Lean side (`ScCert.Kills`) rechecks every condition.
"""
import csv
import itertools
import math
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT_DIR = ROOT / "lean" / "SignedDifferenceSets" / "SelfConjugacyRows"
BOX_DIR = ROOT / "lean" / "SignedDifferenceSets" / "BoxRows"
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
OPEN = "open"


def primes_of(n):
    n, out, p = abs(n), [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def divisors(m):
    return [d for d in range(1, m + 1) if m % d == 0]


def conj_exp(p, e):
    """Least i >= 1 with e | p^i + 1, or None."""
    x = p % e
    for i in range(1, 2 * e + 1):
        if (x + 1) % e == 0:
            return i
        x = x * p % e
    return None


def moments_ok(N, q, sp, Q, t0):
    """Lean's `MomentsOk` (Int `/` is floor division for positive divisors, as Python's //)."""
    if (sp - N * t0) % q:
        return False
    num = Q - 2 * t0 * sp + N * t0 * t0
    if num % (q * q):
        return False
    S1, S2 = (sp - N * t0) // q, num // (q * q)
    m = S1 // N
    B = S2 - 2 * m * S1 + N * m * m
    return (S2 - S1) % 2 == 0 and S1 - N * m <= B and B != 0


def box_ok(N, q, sp, Q, t0, c):
    """Lean's `BoxOk`: the moments test and S2 <= (lo + hi) S1 - N lo hi, y in [lo, hi]."""
    if not moments_ok(N, q, sp, Q, t0):
        return False
    S1, S2 = (sp - N * t0) // q, (Q - 2 * t0 * sp + N * t0 * t0) // (q * q)
    lo, hi = -((c + t0) // q), (c - t0) // q
    return S2 <= (lo + hi) * S1 - N * lo * hi


def cert(v, k, lam, ms):
    n = k - lam
    if n == 0:
        return None
    S = k + lam * (v - 1)
    s = math.isqrt(S) if S >= 0 and math.isqrt(S) ** 2 == S else None
    found, boxed = None, None
    for p in primes_of(n):
        J, rest = 0, abs(n)
        while rest % (p * p) == 0:
            rest //= p * p
            J += 1
        for j in range(J, 0, -1):
            q = p ** j
            for ds in itertools.product(*[divisors(m) for m in ms]):
                h = math.prod(ds)
                if h == 1 or h % p == 0:
                    continue
                i = conj_exp(p, math.lcm(*ds))
                if i is None:
                    continue
                c = v // h
                if 2 * c < q:
                    return ("C5", p, j, i, list(ds), 0)
                if found is None and s is not None:
                    Q = k + lam * (c - 1)
                    if not any(moments_ok(h, q, sp, Q, t) for sp in (s, -s) for t in range(q)):
                        found = ("C13", p, j, i, list(ds), s)
                    elif boxed is None and not any(
                            box_ok(h, q, sp, Q, t, c) for sp in (s, -s) for t in range(q)):
                        boxed = ("C14", p, j, i, list(ds), s)
    return found or boxed


def write_certs(out):
    rows = list(csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8")))
    n = 0
    with open(out, "w", encoding="utf-8") as f:
        for r in rows:
            if r["status"] != OPEN:
                continue
            m = KEY.fullmatch(r["key"])
            v, k, lam = map(int, m.groups()[:3])
            ms = [int(x) for x in m.group(4).split(",")]
            c = cert(v, k, lam, ms)
            if c:
                rule, p, j, i, ds, s = c
                f.write(f"{r['id']} {r['key']} {rule} {p} {j} {i} {','.join(map(str, ds))} {s}\n")
                n += 1
    print(f"{n} rows")


def lean_entry(line):
    nid, key, _rule, p, j, i, ds, s = line.split()
    m = KEY.fullmatch(key)
    k, lam = m.group(2), m.group(3)
    ms = m.group(4).replace(",", ", ")
    return f"  (⟨{nid[1:]}, [{ms}], {k}, {lam}⟩, ⟨{p}, {j}, {i}, [{ds.replace(',', ', ')}], {s}⟩)"


def write_lean(certs, per_part, first=1):
    lines = [l for l in open(certs, encoding="utf-8").read().splitlines() if l.strip()]
    write_parts([l for l in lines if l.split()[2] != "C14"], per_part, first, OUT_DIR,
                "SelfConjugacyRows", "C5 or C13", "Kills", "not_hasSDS")
    write_parts([l for l in lines if l.split()[2] == "C14"], per_part, 1, BOX_DIR,
                "BoxRows", "C14", "BoxKills", "not_hasSDS_of_boxKills")


def write_parts(lines, per_part, first, out_dir, space, rules, kills, sound):
    out_dir.mkdir(exist_ok=True)
    check = "BoxCheck" if kills == "BoxKills" else "SelfConjugacyCheck"
    for idx in range(0, len(lines), per_part):
        part = lines[idx: idx + per_part]
        num = first + idx // per_part
        name = f"part{num:02d}"
        ids = f"{part[0].split()[0]} to {part[-1].split()[0]}"
        body = ",\n".join(lean_entry(l) for l in part)
        text = f"""module

public import SignedDifferenceSets.{check}

/-!
# Rows killed by {rules}, part {num:02d}

{len(part)} open rows ({ids}) with their certificates (generated by
`solver/selfconj.py`); `{name}_kills` checks every one by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets.{space}

/-- Rows and certificates of part {num:02d}. -/
def {name} : List (Row × ScCert) := [
{body}]

set_option maxRecDepth 100000 in
theorem {name}_kills : ∀ x ∈ {name}, x.2.{kills} x.1 := by decide +kernel

/-- No row of part {num:02d} has an SDS. -/
theorem {name}_not_hasSDS {{x : Row × ScCert}} (hx : x ∈ {name})
    (inst : Fintype (Grp x.1.ms)) : ¬ @HasSDS (Grp x.1.ms) _ inst x.1.k x.1.lam :=
  ScCert.{sound} ({name}_kills x hx) inst

end SignedDifferenceSets.{space}
"""
        (out_dir / f"Part{num:02d}.lean").write_text(text, encoding="utf-8", newline="\n")
        print(f"Part{num:02d}.lean: {len(part)} rows")


if __name__ == "__main__":
    if sys.argv[1] == "certs":
        write_certs(sys.argv[2])
    elif sys.argv[1] == "lean":
        write_lean(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 1)
