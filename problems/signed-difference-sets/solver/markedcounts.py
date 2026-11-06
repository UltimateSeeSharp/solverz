"""Certificates for C7 (marked counts per coset) on the open rows, written as Lean chunks.

Under C5's hypotheses the coset sums lie in V = {x in [-c, c] : x = t0 mod q}. Real counts
N_x >= 0 on V with sum N_x = N, sum N_x x = s', sum N_x x^2 = Q must have
sum N_x |x| <= k <= sum N_x maxm(x). By LP duality a failure has a certificate (a, b, g, d):
lower: g + b x + a x^2 <= d |x| on V and g N + b s' + a Q > d k (d = 0: a Farkas ray);
upper: d maxm(x) <= g + b x + a x^2 on V and g N + b s' + a Q < d k.

`markedcounts.py certs <out.txt> [ids.txt]`: one line per open row of instances.csv (only those
whose id starts a line of ids.txt, if given) that C5, C13, C14 leave and a C7 certificate kills:
`id key p j i d1,...,dr s w1;w2;...` with `w = L|U:a,b,g,d` (a x^2 + b x + g against d).
`markedcounts.py lean <certs.txt> <rows per part>`: writes
lean/SignedDifferenceSets/MarkedCountsRows/Part<NN>.lean, each checked by `decide +kernel`.
Standard library only; the Lean side (`McCert.Kills`) rechecks every condition.
"""
import csv
import itertools
import math
import sys
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import selfconj as sc  # noqa: E402

ROOT = sc.ROOT
OUT_DIR = ROOT / "lean" / "SignedDifferenceSets" / "MarkedCountsRows"
OPEN = "open"
LOWER, UPPER = "L", "U"


def maxm(c, x):
    """Lean's `maxMarked`: the most marked elements a coset with sum x holds."""
    return c if (c - x) % 2 == 0 else c - 1


def row(x):
    return (1, x, x * x)


def dot(y, r):
    return sum(a * b for a, b in zip(y, r))


def cross(u, w):
    return (u[1] * w[2] - u[2] * w[1], u[2] * w[0] - u[0] * w[2], u[0] * w[1] - u[1] * w[0])


def solve(rs, fs):
    """y with y . r = f for each given row (len <= 3), free coordinates set to 0; None if
    the rows are dependent."""
    m = len(rs)
    M = [[Fraction(v) for v in r] + [Fraction(f)] for r, f in zip(rs, fs)]
    piv = []
    for i in range(m):
        col = next((j for j in range(3) if j not in piv and M[i][j] != 0), None)
        if col is None:
            return None
        for i2 in range(m):
            if i2 != i and M[i2][col] != 0:
                fct = M[i2][col] / M[i][col]
                M[i2] = [a - fct * b for a, b in zip(M[i2], M[i])]
        piv.append(col)
    y = [Fraction(0)] * 3
    for i, col in enumerate(piv):
        y[col] = M[i][3] / M[i][col]
    return tuple(y)


def dual_max(V, f, b):
    """max b.y subject to y . row(x) <= f(x) on V: ("ray", y) when unbounded, else
    ("opt", y, value). y = (g, b, a) is the quadratic g + b x + a x^2."""
    rs = [row(x) for x in V]
    if len(V) >= 3:
        for r1, r2 in itertools.combinations(rs, 2):
            u = cross(r1, r2)
            for y in (u, tuple(-a for a in u)):
                if dot(b, y) > 0 and all(dot(y, r) <= 0 for r in rs):
                    return ("ray", y)
        best = None
        for tri in itertools.combinations(range(len(V)), 3):
            y = solve([rs[i] for i in tri], [f(V[i]) for i in tri])
            if y is None or any(dot(y, r) > f(x) for x, r in zip(V, rs)):
                continue
            val = dot(b, y)
            if best is None or val > best[2]:
                best = ("opt", y, val)
        return best
    # |V| <= 2: the rows do not span; b outside their span gives a ray in the lineality space.
    if len(V) == 0:
        return ("ray", (1, 0, 0))
    if len(V) == 1:
        r1 = rs[0]
        rr = dot(r1, r1)
        y = tuple(Fraction(bi) - Fraction(dot(b, r1), rr) * ri for bi, ri in zip(b, r1))
        if dot(b, y) > 0:
            return ("ray", y)
        lam = Fraction(dot(b, r1), rr)
        if lam < 0:
            return ("ray", tuple(-a for a in r1))
        return ("opt", (Fraction(f(V[0])), Fraction(0), Fraction(0)), lam * f(V[0]))
    r1, r2 = rs
    u = cross(r1, r2)
    if dot(b, u) != 0:
        return ("ray", u if dot(b, u) > 0 else tuple(-a for a in u))
    # b = u1 r1 + u2 r2
    co = solve([(r1[0], r2[0], 0), (r1[1], r2[1], 0)], [b[0], b[1]])
    u1, u2 = co[0], co[1]
    if u1 < 0 or u2 < 0:
        y = solve([r1, r2], [-1 if u1 < 0 else 0, -1 if u2 < 0 else 0])
        return ("ray", y)
    y = solve([r1, r2], [f(V[0]), f(V[1])])
    return ("opt", y, u1 * f(V[0]) + u2 * f(V[1]))


def integral(y, d):
    """Scale the rational quadratic y and the factor d to coprime integers."""
    den = math.lcm(*[Fraction(a).denominator for a in y], Fraction(d).denominator)
    ys = [int(Fraction(a) * den) for a in y]
    dd = int(Fraction(d) * den)
    g = math.gcd(*ys, dd)
    return tuple(a // g for a in ys), dd // g


def check_weight(kind, w, N, q, sp, Q, t0, c, k):
    """Lean's `Weights.LowerChk` / `UpperChk`."""
    a, b, g, d = w
    if d < 0:
        return False
    tot = g * N + b * sp + a * Q
    V = [x for x in range(-c, c + 1) if (x - t0) % q == 0]
    ev = [g + b * x + a * x * x for x in V]
    if kind == LOWER:
        return all(e <= d * abs(x) for e, x in zip(ev, V)) and d * k < tot
    return all(d * maxm(c, x) <= e for e, x in zip(ev, V)) and tot < d * k


def basic_counts(tri, N, sp, Q):
    """The counts on three values with the given moments (Lagrange interpolation); None if
    one is negative."""
    nums = []
    for i in range(3):
        xi, xj, xk = tri[i], tri[(i + 1) % 3], tri[(i + 2) % 3]
        num, den = Q - (xj + xk) * sp + xj * xk * N, (xi - xj) * (xi - xk)
        if num * den < 0:
            return None
        nums.append((num, den))
    return [Fraction(num, den) for num, den in nums]


def dual_from_basis(V, f, tri):
    """The quadratic through (x, f(x)) on tri, if it stays below f on V."""
    y = solve([row(x) for x in tri], [f(x) for x in tri])
    if all(dot(y, row(x)) <= f(x) for x in V):
        return y
    return None


def weight(N, q, sp, Q, t0, c, k):
    """A lower or upper certificate for (s', t0), or None when the LP does not kill it."""
    V = [x for x in range(-c, c + 1) if (x - t0) % q == 0]
    b = (N, sp, Q)
    if len(V) >= 3:
        # The primal optimum sits on a basic solution (three values, |V| >= 3): screen first.
        lo, hi = None, None
        for tri in itertools.combinations(V, 3):
            cnt = basic_counts(tri, N, sp, Q)
            if cnt is None:
                continue
            vl = sum(n * abs(x) for n, x in zip(cnt, tri))
            vu = sum(n * maxm(c, x) for n, x in zip(cnt, tri))
            if lo is None or vl < lo[0]:
                lo = (vl, tri)
            if hi is None or vu > hi[0]:
                hi = (vu, tri)
            if lo[0] <= k <= hi[0]:
                return None
        if lo is not None and lo[0] > k:
            y = dual_from_basis(V, abs, lo[1])
            if y is not None:
                y, d = integral(y, 1)
                return (LOWER, (y[2], y[1], y[0], d))
        if lo is not None and hi[0] < k:
            y = dual_from_basis(V, lambda x: -maxm(c, x), hi[1])
            if y is not None:
                y, d = integral(tuple(-a for a in y), 1)
                return (UPPER, (y[2], y[1], y[0], d))
    res = dual_max(V, abs, b)
    if res[0] == "ray":
        y, d = integral(res[1], 0)
        return (LOWER, (y[2], y[1], y[0], d))
    if res[2] > k:
        y, d = integral(res[1], 1)
        return (LOWER, (y[2], y[1], y[0], d))
    res = dual_max(V, lambda x: -maxm(c, x), b)
    if res[0] == "ray":  # cannot happen here: the lower LP was feasible
        y, d = integral(res[1], 0)
        return (LOWER, (y[2], y[1], y[0], d))
    if -res[2] < k:
        y, d = integral(tuple(-a for a in res[1]), 1)
        return (UPPER, (y[2], y[1], y[0], d))
    return None


def cert(v, k, lam, ms):
    """First (p, j, i, ds) under C5's hypotheses on which every (s', t0) passing the box test
    has a certificate, with the certificates; None if there is none."""
    n = k - lam
    S = k + lam * (v - 1)
    if n == 0 or S < 0 or math.isqrt(S) ** 2 != S:
        return None
    s = math.isqrt(S)
    for p in sc.primes_of(n):
        J, rest = 0, abs(n)
        while rest % (p * p) == 0:
            rest //= p * p
            J += 1
        for j in range(J, 0, -1):
            q = p ** j
            for ds in itertools.product(*[sc.divisors(m) for m in ms]):
                h = math.prod(ds)
                if h == 1 or h % p == 0:
                    continue
                i = sc.conj_exp(p, math.lcm(*ds))
                if i is None:
                    continue
                c = v // h
                Q = k + lam * (c - 1)
                ws, ok = [], True
                for sp in (s, -s):
                    for t in range(q):
                        if not sc.box_ok(h, q, sp, Q, t, c):
                            continue
                        w = weight(h, q, sp, Q, t, c, k)
                        if w is None or not check_weight(*w, h, q, sp, Q, t, c, k):
                            ok = False
                            break
                        if w not in ws:
                            ws.append(w)
                    if not ok:
                        break
                if ok:
                    return (p, j, i, list(ds), s, ws)
    return None


def write_certs(out, ids=None):
    rows = list(csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8")))
    if ids:
        keep = {l.split()[0] for l in open(ids, encoding="utf-8") if l.strip()}
        rows = [r for r in rows if r["id"] in keep]
    n = 0
    with open(out, "w", encoding="utf-8") as f:
        for r in rows:
            if r["status"] != OPEN:
                continue
            m = sc.KEY.fullmatch(r["key"])
            v, k, lam = map(int, m.groups()[:3])
            ms = [int(x) for x in m.group(4).split(",")]
            if sc.cert(v, k, lam, ms):
                continue
            c = cert(v, k, lam, ms)
            if c:
                p, j, i, ds, s, ws = c
                wtxt = ";".join(f"{kind}:{','.join(map(str, w))}" for kind, w in ws)
                f.write(f"{r['id']} {r['key']} {p} {j} {i} {','.join(map(str, ds))} {s} "
                        f"{wtxt}\n")
                n += 1
    print(f"{n} rows")


def lean_entry(line):
    nid, key, p, j, i, ds, s, wtxt = line.split()
    m = sc.KEY.fullmatch(key)
    k, lam = m.group(2), m.group(3)
    ms = m.group(4).replace(",", ", ")
    ws = ", ".join(f"⟨{w[2:].replace(',', ', ')}⟩" for w in wtxt.split(";"))
    return (f"  (⟨{nid[1:]}, [{ms}], {k}, {lam}⟩,\n"
            f"    ⟨⟨{p}, {j}, {i}, [{ds.replace(',', ', ')}], {s}⟩, [{ws}]⟩)")


def write_lean(certs, per_part):
    lines = [l for l in open(certs, encoding="utf-8").read().splitlines() if l.strip()]
    OUT_DIR.mkdir(exist_ok=True)
    for idx in range(0, len(lines), per_part):
        part = lines[idx: idx + per_part]
        num = 1 + idx // per_part
        name = f"part{num:02d}"
        ids = f"{part[0].split()[0]} to {part[-1].split()[0]}"
        body = ",\n".join(lean_entry(l) for l in part)
        text = f"""module

public import SignedDifferenceSets.MarkedCountsCheck

/-!
# Rows killed by C7, part {num:02d}

{len(part)} open rows ({ids}) with their certificates (generated by
`solver/markedcounts.py`); `{name}_kills` checks every one by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets.MarkedCountsRows

/-- Rows and certificates of part {num:02d}. -/
def {name} : List (Row × McCert) := [
{body}]

set_option maxRecDepth 100000 in
theorem {name}_kills : ∀ x ∈ {name}, x.2.Kills x.1 := by decide +kernel

/-- No row of part {num:02d} has an SDS. -/
theorem {name}_not_hasSDS {{x : Row × McCert}} (hx : x ∈ {name})
    (inst : Fintype (Grp x.1.ms)) : ¬ @HasSDS (Grp x.1.ms) _ inst x.1.k x.1.lam :=
  McCert.not_hasSDS ({name}_kills x hx) inst

end SignedDifferenceSets.MarkedCountsRows
"""
        (OUT_DIR / f"Part{num:02d}.lean").write_text(text, encoding="utf-8", newline="\n")
        print(f"Part{num:02d}.lean: {len(part)} rows")


if __name__ == "__main__":
    if sys.argv[1] == "certs":
        write_certs(sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else None)
    elif sys.argv[1] == "lean":
        write_lean(sys.argv[2], int(sys.argv[3]))
