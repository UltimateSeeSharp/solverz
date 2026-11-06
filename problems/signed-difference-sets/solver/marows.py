"""Rows killed by C21 (Ma's lemma on a quotient ZMod (r p) x K), written as Lean chunks.

`marows.py [rows per part]`: for each open row of instances.csv, finds the prime p | k - lambda
(e = v_p(k - lambda) >= 2, b = e // 2), the cyclic quotient C_{p^j} (r = p^(j-1)) and the largest
quotient K of the p'-part with p^i = -1 on K, minimising N = (p - 1) r among the kills
2 v / (p^j |K|) < p^b. The quotient map projects factor s onto C_{p^j} and each factor onto its part
of K; the preimages of the unit vectors come from the CRT. Writes, under lean/SignedDifferenceSets:
- MaRows/Polys.lean: CycloFacts for each (p, r) used, from certificates f, g, u (w = 1) at r = 1
  (and r = 2 for p = 2), then `CycloFacts.mul` from r to p r;
- MaRows/Part<NN>.lean: the rows, one `decide +kernel` per part, each part's theorem given MaRule;
- MaRows/All.lean: each part's theorem without the hypothesis, by `maRule`.
Every row and certificate is rechecked here by a mirror of Lean's `MaRowCert.Kills` and `MaCert`.
Standard library only.
"""
import csv
import math
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT_DIR = ROOT / "lean" / "SignedDifferenceSets" / "MaRows"
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
OPEN = "open"
PER_PART = 250
WIDTH = 100


# --- Mirror of PolyCert.lean ---------------------------------------------------------------

def add_l(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def smul_l(c, b):
    return [c * x for x in b]


def mul_l(a, b):
    out = []
    for x in reversed(a):
        out = add_l(smul_l(x, b), [0] + out)
    return out


def pow_l(a, n):
    out = [1]
    for _ in range(n):
        out = mul_l(out, a)
    return out


def mono_l(n):
    return [0] * n + [1]


def geom_l(q, n):
    out = []
    for _ in range(n):
        out = add_l([1], mul_l(q, out))
    return out


def psi_l(p, r):
    return geom_l(mono_l(r), p)


def pi_l(p, r):
    return pow_l([-1, 1], (p - 1) * r)


def ma_cert(p, r, f, g, u, w):
    a = add_l(add_l(mul_l(pi_l(p, r), f), mul_l(psi_l(p, r), g)), [-p])
    b = add_l(pi_l(p, r), smul_l(-1, add_l(smul_l(p, u), mul_l(psi_l(p, r), w))))
    return all(x == 0 for x in a) and all(x == 0 for x in b)


def divmod_monic(a, m):
    """Quotient and remainder of a by the monic m."""
    a, q = a[:], [0] * max(1, len(a) - len(m) + 1)
    for i in range(len(a) - len(m), -1, -1):
        c = a[i + len(m) - 1]
        if c:
            q[i] = c
            for j, y in enumerate(m):
                a[i + j] -= c * y
    return q, a[:len(m) - 1]


def trim(a):
    while len(a) > 1 and a[-1] == 0:
        a = a[:-1]
    return a


def poly_cert(p, r):
    """f, g, u with (X-1)^N f + Psi g = p and (X-1)^N = p u + Psi (w = 1)."""
    psi, pi = trim(psi_l(p, r)), pi_l(p, r)
    f = [1]
    for k in range(1, p * r):
        if k % p:
            _, f = divmod_monic(mul_l(f, [1] * k), psi)
    f = smul_l((-1) ** ((p - 1) * r), f)
    rest = add_l([p], smul_l(-1, mul_l(pi, f)))
    g, rem = divmod_monic(rest, psi)
    assert not any(rem), (p, r)
    d = add_l(pi, smul_l(-1, psi))
    assert all(x % p == 0 for x in d), (p, r)
    f, g, u = trim(f), trim(g), trim([x // p for x in d])
    assert ma_cert(p, r, f, g, u, [1]), (p, r)
    return f, g, u


# --- Mirror of LinearMaps.lean and MaCheck.lean ----------------------------------------------

def head(xs, default):
    return xs[0] if xs else default


def is_prime_td(p):
    return 2 <= p and all(p % d != 0 for d in range(2, p))


def form_ok(n, as_, ms):
    if not ms:
        return True
    if n == 0:
        ok = head(as_, 0) * ms[0] == 0
    else:
        ok = (head(as_, 0) * ms[0]) % n == 0
    return ok if len(ms) == 1 else ok and form_ok(n, as_[1:], ms[1:])


def dot_l(ms, as_, xs):
    if not ms:
        return 0
    x = head(as_, 0) * head(xs, 0)
    return x if len(ms) == 1 else x + dot_l(ms[1:], as_[1:], xs[1:])


def map_ok(ms, ds, A):
    if not ds:
        return True
    ok = form_ok(ds[0], head(A, []), ms)
    return ok if len(ds) == 1 else ok and map_ok(ms, ds[1:], A[1:])


def eval_map(ms, xs, ds, A):
    if not ds:
        return []
    v = [dot_l(ms, head(A, []), xs)]
    return v if len(ds) == 1 else v + eval_map(ms, xs, ds[1:], A[1:])


def nat_mod(a, d):
    return a if d == 0 else a % d


def mod_eqs(ds, xs, ys):
    if not ds:
        return True
    ok = nat_mod(head(xs, 0), ds[0]) == nat_mod(head(ys, 0), ds[0])
    return ok if len(ds) == 1 else ok and mod_eqs(ds[1:], xs[1:], ys[1:])


def unit_l(t):
    return [0] * t + [1]


def surj_cert(ms, ds, A, P):
    return all(mod_eqs(ds, eval_map(ms, P[t] if t < len(P) else [], ds, A), unit_l(t))
               for t in range(len(ds)))


def kills(ms, k, lam, c):
    p, r, i, e, b, ks, A, P = c
    ds = [r * p] + ks
    q = r * p * math.prod(ks)
    return (is_prime_td(p) and r > 0 and i > 0 and all(m > 0 for m in ms) and ks != []
            and all((p ** i + 1) % d == 0 for d in ks) and map_ok(ms, ds, A)
            and surj_cert(ms, ds, A, P) and math.prod(ms) % q == 0
            and (k - lam) % p ** e == 0 and k != lam and 2 * b <= e
            and 2 * (math.prod(ms) // q) < p ** b)


# --- Finding the certificates -----------------------------------------------------------------

def vp(x, p):
    c = 0
    while x % p == 0:
        x //= p
        c += 1
    return c


def primes_of(n):
    n, out, d = abs(n), [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def conj_exp(p, m):
    """Least i >= 1 with p^i = -1 mod m, or None."""
    if m == 1:
        return 1
    x = p % m
    for i in range(1, m + 1):
        if (x + 1) % m == 0:
            return i
        x = x * p % m
    return None


def crt(a, m, b, n):
    """x mod m n with x = a mod m, x = b mod n (gcd(m, n) = 1)."""
    return next(x for x in range(m * n) if x % m == a % m and x % n == b % n)


def cert(ms, k, lam):
    n, v = k - lam, math.prod(ms)
    if n == 0:
        return None
    best = None
    for p in primes_of(n):
        e = vp(n, p)
        b, J = e // 2, max(vp(m, p) for m in ms)
        if b == 0 or J == 0:
            continue
        pp = [m // p ** vp(m, p) for m in ms]
        expo = math.lcm(*pp)
        mm = max((d for d in range(1, expo + 1) if expo % d == 0 and conj_exp(p, d)),
                 key=lambda d: (math.prod(math.gcd(x, d) for x in pp), -d))
        kap = [math.gcd(x, mm) for x in pp]
        size = math.prod(kap)
        for j in range(1, J + 1):
            if 2 * (v // (p ** j * size)) < p ** b:
                key = ((p - 1) * p ** (j - 1), p)
                if best is None or key < best[0]:
                    best = (key, p, j, e, b, kap)
                break
    if best is None:
        return None
    _, p, j, e, b, kap = best
    r, pj = p ** (j - 1), p ** j
    s = next(t for t, m in enumerate(ms) if m % pj == 0)
    src = [t for t, x in enumerate(kap) if x > 1]
    ks = [kap[t] for t in src] or [1]
    src = src or [s]
    i = conj_exp(p, math.lcm(*ks))
    A = [[0] * s + [1]] + [[0] * t + [1] for t in src]
    P = [[0] * s + [crt(1, pj, 0, kap[s])]]
    for t, d in zip(src, ks):
        P.append([0] * t + [crt(1, d, 0, pj) if t == s else 1 % d])
    c = (p, r, i, e, b, ks, A, P)
    assert kills(ms, k, lam, c), (ms, k, lam, c)
    return c


# --- Writing Lean -----------------------------------------------------------------------------

def lst(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


LIMB = 10 ** 80


def int_lean(c):
    """A coefficient as Lean: a literal, or `ofLimbs` of base-10^80 digits when too long."""
    if abs(c) < LIMB:
        return str(c)
    a, limbs = abs(c), []
    while a:
        limbs.append(a % LIMB)
        a //= LIMB
    limbs.reverse()
    assert of_limbs(limbs) == abs(c)
    txt = f"(ofLimbs {lst(limbs)} : ℤ)"
    return f"-{txt}" if c < 0 else txt


def zlst(xs):
    return "[" + ", ".join(map(int_lean, xs)) + "]"


def of_limbs(limbs):
    a = 0
    for d in limbs:
        a = a * LIMB + d
    return a


NBSP = chr(0xA0)
NL = chr(10)


def tight(xs):
    """A list that `wrap` keeps on one line."""
    return lst(xs).replace(" ", NBSP)


def wrap(text, indent):
    """Breaks `text` at spaces (not at NBSP) so no line passes WIDTH."""
    lines, cur = [], indent
    for tok in text.split(" "):
        if len(cur) + len(tok) + 1 > WIDTH and cur.strip():
            lines.append(cur.rstrip())
            cur = indent + "  "
        cur += tok + " "
    lines.append(cur.rstrip())
    return NL.join(lines).replace(NBSP, " ")


def poly_name(p, r):
    return f"P{p}R{r}"


def base_r(p):
    """The certificate's r for prime p: `CycloFacts.mul` needs (p - 1) r >= 2 to step on."""
    return 2 if p == 2 else 1


def write_polys(pairs):
    blocks, cases = [], []
    for p in sorted({p for p, _ in pairs}):
        top = max(r for q, r in pairs if q == p)
        rs = [1] + ([2] if p == 2 and top >= 2 else [])
        for r in rs:
            f, g, u = poly_cert(p, r)
            nm = poly_name(p, r)
            for lbl, xs in (("f", f), ("g", g), ("u", u)):
                blocks.append(f"/-- `{lbl}` at `(p, r) = ({p}, {r})`. -/{NL}"
                              f"def {lbl}{nm} : List ℤ :={NL}{wrap(zlst(xs), '  ')}{NL}")
            blocks.append(f"theorem maCert{nm} : MaCert {p} {r} f{nm} g{nm} u{nm} [1] := by{NL}"
                          f"  decide +kernel{NL}")
            blocks.append(f"theorem cycloFacts{nm} : CycloFacts {p} {r} := "
                          f"maCert{nm}.cycloFacts{NL}")
        r = base_r(p)
        while r * p <= top:
            assert is_prime_td(p) and (p - 1) * r >= 2, (p, r)
            blocks.append(f"theorem cycloFacts{poly_name(p, r * p)} : CycloFacts {p} {r * p} :={NL}"
                          f"  cycloFacts{poly_name(p, r)}.mul (by norm_num) (by norm_num){NL}")
            r *= p
    cases = [f"cycloFacts{poly_name(p, r)}" for p, r in pairs]
    pairs_txt = wrap(lst(f"({p},{NBSP}{r})" for p, r in pairs), "  ")
    rc = " | ".join(["rfl"] * len(pairs))
    text = f"""module

public import SignedDifferenceSets.MaCheck

/-!
# C21's cyclotomic facts at the rows' `(p, r)`

`CycloFacts p r` for each pair the rows of `MaRows` use: at `r = 1` (and `r = 2` for `p = 2`)
from `MaCert`'s `f`, `g`, `u` (`w = 1`), checked by `decide +kernel`; above, by `CycloFacts.mul`
from `r` to `p r`. Generated by `solver/marows.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.MaRows

{NL.join(blocks)}
/-- The pairs `(p, r)` the rows use. -/
def maPairs : List (ℕ × ℕ) :=
{pairs_txt}

theorem cycloFacts_of_mem_maPairs {{pr : ℕ × ℕ}} (h : pr ∈ maPairs) :
    CycloFacts pr.1 pr.2 := by
  simp only [maPairs, List.mem_cons, List.not_mem_nil, or_false] at h
{wrap("rcases h with " + rc, "  ")}
{wrap("exacts [" + ", ".join(cases) + "]", "  ")}

end SignedDifferenceSets.MaRows
"""
    (OUT_DIR / "Polys.lean").write_text(text, encoding="utf-8", newline=NL)
    print("Polys.lean:", len(pairs), "pairs")


def entry(rid, ms, k, lam, c):
    p, r, i, e, b, ks, A, P = c
    row = f"(⟨{rid}, {lst(ms)}, {k}, {lam}⟩,"
    cer = (f"⟨{p}, {r}, {i}, {e}, {b}, {lst(ks)}, {lst(tight(a) for a in A)}, "
           f"{lst(tight(x) for x in P)}⟩)")
    one = f"  {row} {cer}"
    return one.replace(NBSP, " ") if len(one) <= WIDTH - 1 else f"  {row}\n{wrap(cer, '    ')}"


def write_parts(entries, per_part):
    for num, start in enumerate(range(0, len(entries), per_part), 1):
        part = entries[start:start + per_part]
        name = f"part{num:02d}"
        body = ",\n".join(e for _, e in part)
        text = f"""module

public import SignedDifferenceSets.MaRows.Polys

/-!
# Rows killed by C21, part {num:02d}

{len(part)} open rows (N{part[0][0]} to N{part[-1][0]}) with their certificates (generated by
`solver/marows.py`); `{name}_kills` checks every one by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets.MaRows

/-- Rows and certificates of part {num:02d}. -/
def {name} : List (Row × MaRowCert) := [
{body}]

set_option maxRecDepth 100000 in
theorem {name}_kills : ∀ x ∈ {name}, x.2.Kills x.1 ∧ (x.2.p, x.2.r) ∈ maPairs := by
  decide +kernel

/-- No row of part {num:02d} has an SDS, given C21. -/
theorem {name}_not_hasSDS (hrule : MaRule) {{x : Row × MaRowCert}} (hx : x ∈ {name})
    (inst : Fintype (Grp x.1.ms)) : ¬ @HasSDS (Grp x.1.ms) _ inst x.1.k x.1.lam :=
  MaRowCert.not_hasSDS hrule ({name}_kills x hx).1
    (cycloFacts_of_mem_maPairs ({name}_kills x hx).2) inst

end SignedDifferenceSets.MaRows
"""
        (OUT_DIR / f"Part{num:02d}.lean").write_text(text, encoding="utf-8", newline="\n")
        print(f"Part{num:02d}.lean: {len(part)} rows")


def write_all(counts):
    names = [f"part{num:02d}" for num in range(1, len(counts) + 1)]
    imports = NL.join(f"public import SignedDifferenceSets.MaRows.Part{n[4:]}" for n in names)
    thms = NL.join(f"""/-- No row of part {n[4:]} has an SDS. -/
theorem not_hasSDS_of_mem_{n} {{x : Row × MaRowCert}} (hx : x ∈ {n})
    (inst : Fintype (Grp x.1.ms)) : ¬ @HasSDS (Grp x.1.ms) _ inst x.1.k x.1.lam :=
  {n}_not_hasSDS maRule hx inst
""" for n in names)
    rc = " | ".join(["h"] * len(names))
    cases = ", ".join(f"not_hasSDS_of_mem_{n} h inst".replace(" ", NBSP) for n in names)
    text = f"""module

public import SignedDifferenceSets.MaLemma
{imports}

/-!
# Rows killed by C21

C21's rule is `maRule` (`MaLemma.lean`), so each part's theorem holds without its hypothesis.
`maRows` lists all {sum(counts)} rows; generated by `solver/marows.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.MaRows

{thms}
/-- Every row C21 kills, with its certificate. -/
def maRows : List (Row × MaRowCert) :=
{wrap(" ++ ".join(names), "  ")}

/-- No row of `maRows` has an SDS. -/
theorem not_hasSDS_of_mem_maRows {{x : Row × MaRowCert}} (hx : x ∈ maRows)
    (inst : Fintype (Grp x.1.ms)) : ¬ @HasSDS (Grp x.1.ms) _ inst x.1.k x.1.lam := by
  simp only [maRows, List.mem_append, or_assoc] at hx
{wrap("rcases hx with " + rc, "  ")}
{wrap("exacts [" + cases + "]", "  ")}

end SignedDifferenceSets.MaRows
"""
    (OUT_DIR / "All.lean").write_text(text, encoding="utf-8", newline=NL)
    print("All.lean:", sum(counts), "rows")


def main(per_part):
    entries, pairs, ids = [], set(), []
    for row in csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8")):
        if row["status"] != OPEN:
            continue
        m = KEY.fullmatch(row["key"])
        k, lam = int(m.group(2)), int(m.group(3))
        ms = [int(x) for x in m.group(4).split(",")]
        c = cert(ms, k, lam)
        if c:
            rid = int(row["id"][1:])
            entries.append((rid, entry(rid, ms, k, lam, c)))
            pairs.add((c[0], c[1]))
            ids.append(row["id"])
    OUT_DIR.mkdir(exist_ok=True)
    write_polys(sorted(pairs))
    write_parts(entries, per_part)
    write_all([len(entries[i:i + per_part]) for i in range(0, len(entries), per_part)])
    (OUT_DIR.parent.parent.parent / "scratch" / "marows_ids.txt").write_text(
        "\n".join(ids) + "\n", encoding="utf-8")
    print(len(entries), "rows,", len(pairs), "pairs")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else PER_PART)
