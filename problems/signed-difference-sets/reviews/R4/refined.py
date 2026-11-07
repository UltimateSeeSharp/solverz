# Refinements of rule SC (proposals, not part of the claim). With all a_h = t mod p^j and
# sum a_h = s (s^2 = n + lam v): h t = s mod p^j. R1: kill if [-c, c] holds at most one
# integer = t mod p^j (rule SC is the special case "never two", p^j > 2c). R2: also require
# counts N_x >= 0 on those values with sum N = h, sum N x = s, sum N x^2 = n + lam c, >= 2 values.
import csv, sys, math, re, collections, functools
sys.path.insert(0, ".")
from indep import factor, selfconj, quotient_types
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

def feasible_counts(vals, h, s, q2):
    # exists N_x >= 0, sum N = h, sum N x = s, sum N x^2 = q2, using >= 2 distinct values.
    # Enumerate the counts of all but the last 3 values; solve the 3x3 Vandermonde exactly.
    from fractions import Fraction
    vals = sorted(vals); r = len(vals)
    if r <= 1: return False
    head, tail = vals[:-3] if r > 3 else [], vals[-3:] if r >= 3 else vals
    def rec(i, left, sl, ql, used):
        if i == len(head):
            if len(tail) == 2:
                x, y = tail; ny = Fraction(sl - x * left, y - x); nx = left - ny
                cands = [(nx, ny)] if ny.denominator == 1 and nx >= 0 and ny >= 0 else []
                return any(nx * x * x + ny * y * y == ql and used + (nx > 0) + (ny > 0) >= 2 for nx, ny in cands)
            x, y, z = tail  # solve a + b + c = left, ax + by + cz = sl, ax^2 + by^2 + cz^2 = ql
            det = (y - x) * (z - x) * (z - y)
            c = Fraction(ql - (x + y) * sl + x * y * left, (z - x) * (z - y))
            b = Fraction(sl - x * left - c * (z - x), y - x); a = left - b - c
            ok = all(t.denominator == 1 and t >= 0 for t in (a, b, c))
            return ok and used + (a > 0) + (b > 0) + (c > 0) >= 2
        x = head[i]
        for cnt in range(left + 1):
            if x * x * cnt > ql: break
            if rec(i + 1, left - cnt, sl - cnt * x, ql - cnt * x * x, used + (cnt > 0)): return True
        return False
    return rec(0, h, s, q2, 0)

def verdict(v, k, lam, shape, level):
    n = k - lam
    if n <= 0: return None
    S = n + lam * v
    if S < 0 or math.isqrt(S) ** 2 != S: return "s-not-integer"
    s = math.isqrt(S)
    Q = quotient_types(shape)
    for p, e in factor(n).items():
        j = e // 2
        if j == 0: continue
        q = p ** j
        for h, m in Q:
            if h == 1 or h % p == 0 or not selfconj(p, m): continue
            c = v // h
            t = s * pow(h, -1, q) % q
            vals = [x for x in range(-c, c + 1) if (x - t) % q == 0]
            if q > 2 * c: return f"SC p={p} j={j} h={h}"
            if len(vals) <= 1: return f"R1 p={p} j={j} h={h}"
            if level >= 2 and not feasible_counts(tuple(vals), h, s, n + lam * c):
                return f"R2 p={p} j={j} h={h}"
    return None

if __name__ == "__main__":
    level = int(sys.argv[2])
    cnt, ex, bad = collections.Counter(), {}, []
    for r in csv.DictReader(open(sys.argv[1], encoding="utf-8")):
        mm = KEY.fullmatch(r["key"]); v, k, lam = map(int, mm.groups()[:3]); shape = [int(x) for x in mm.group(4).split(",")]
        w = verdict(v, k, lam, shape, level)
        if not w: continue
        tag = w.split()[0]; cnt[(r["status"], tag)] += 1
        ex.setdefault((r["status"], tag), []).append((r["id"], r["key"], w))
        if r["status"] == "exists" and tag != "s-not-integer": bad.append((r["id"], r["key"], w))
    print(dict(cnt)); print("existing killed:", bad)
    for key in ex:
        print(key, ex[key][:4])
