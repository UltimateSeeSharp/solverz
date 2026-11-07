"""Independent implementation of SC, SC++ (R1/R2), A1 and A2 (refuter, extensions).
Feasibility: MILP (HiGHS) for the full run; exact enumeration / min-count DP to confirm kills."""
import sys, math
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
sys.path.insert(0, '.')
from xcommon import primefac, self_conj, quotient_types, s_of

def maxm(x, c):
    return c if (c - x) % 2 == 0 else c - 1

def V_of(c, h, s, q):
    return [x for x in range(-c, c + 1) if (h * x - s) % q == 0]

def check_counts(V, N, h, s, Q, k=None, c=None):
    if any(x < 0 for x in N) or sum(N) != h: return False
    if sum(a * x for a, x in zip(N, V)) != s or sum(a * x * x for a, x in zip(N, V)) != Q: return False
    if k is not None:
        A = sum(a * abs(x) for a, x in zip(N, V)); M = sum(a * maxm(x, c) for a, x in zip(N, V))
        if not (A <= k <= M and (k - A) % 2 == 0): return False
    return True

def feas_milp(V, h, s, Q, k=None, c=None):
    """True (verified solution), False (HiGHS infeasible), None (unsure)."""
    nv = len(V)
    rowsA = [[1] * nv, list(V), [x * x for x in V]]; lb = [h, s, Q]; ub = [h, s, Q]
    nvar = nv
    if k is not None:
        nvar = nv + 1   # w: k - sum|x|N = 2w
        rowsA = [r + [0] for r in rowsA]
        rowsA.append([abs(x) for x in V] + [2]); lb.append(k); ub.append(k)
        rowsA.append([maxm(x, c) for x in V] + [0]); lb.append(k); ub.append(np.inf)
    A = np.array(rowsA, dtype=float)
    res = milp(np.zeros(nvar), constraints=LinearConstraint(A, lb, ub), integrality=np.ones(nvar),
               bounds=Bounds(np.zeros(nvar), np.full(nvar, max(h, k or 0) + 1.0)))
    if res.status == 2: return False
    if res.status == 0:
        N = [int(round(x)) for x in res.x[:nv]]
        return True if check_counts(V, N, h, s, Q, k, c) else None
    return None

def _solve3(xs, h, s, Q):
    """Exact nonneg integer counts on <= 3 distinct values meeting the 3 moments, or None."""
    if len(xs) == 1:
        a = xs[0]
        return [h] if (h * a == s and h * a * a == Q) else None
    if len(xs) == 2:
        a, b = xs
        num = s - b * h; den = a - b
        if num % den: return None
        Na = num // den; Nb = h - Na
        if Na < 0 or Nb < 0 or a * a * Na + b * b * Nb != Q: return None
        return [Na, Nb]
    a, b, cc = xs
    out = []
    for x, y, z in ((a, b, cc), (b, a, cc), (cc, a, b)):
        num = Q - (y + z) * s + y * z * h; den = (x - y) * (x - z)
        if num % den: return None
        out.append(num // den)
    if min(out) < 0: return None
    return out

def feas_enum(V, h, s, Q, k=None, c=None, limit=5 * 10 ** 6):
    """Exact: enumerate counts of all but the 3 smallest-|x| values, solve the 3 exactly.
    True/False, or None if the node limit is hit."""
    Vs = sorted(V, key=lambda x: (abs(x), x))
    free, piv = Vs[3:][::-1], Vs[:3]
    nodes = [0]
    def rec(i, hh, ss, QQ, acc):
        nodes[0] += 1
        if nodes[0] > limit: raise OverflowError
        if i == len(free):
            sol = _solve3(piv, hh, ss, QQ)
            return sol is not None and check_counts(free + piv, acc + sol, h, s, Q, k, c)
        x = free[i]; x2 = x * x
        for N in range(0, hh + 1):
            if N * x2 > QQ: break
            if rec(i + 1, hh - N, ss - N * x, QQ - N * x2, acc + [N]): return True
        return False
    try:
        return rec(0, h, s, Q, [])
    except OverflowError:
        return None

def feas_dp(V, h, s, Q):
    """Exact for R2 (no A2 extras): a = t0 + q y, y in [0, R]; the least number of y >= 1 with
    sum S1 and sum of squares S2 must be <= h (the rest y = 0, i.e. x = t0, which is in V)."""
    V = sorted(V); t0 = V[0]; R = len(V) - 1
    q = V[1] - V[0] if len(V) > 1 else 1
    if (s - h * t0) % q: return False
    S1 = (s - h * t0) // q
    num = Q - 2 * t0 * s + h * t0 * t0
    if num % (q * q): return False
    S2 = num // (q * q)
    if S1 < 0 or S2 < 0: return False
    if S1 == 0: return S2 == 0
    if S1 * (S2 + 1) > 8 * 10 ** 7: return None
    INF = 30000
    dp = np.full((S1 + 1, S2 + 1), INF, dtype=np.int16); dp[0, 0] = 0
    for a in range(1, S1 + 1):
        row = dp[a]
        for y in range(1, min(R, a) + 1):
            y2 = y * y
            if y2 > S2: break
            np.minimum(row[y2:], dp[a - y, :S2 + 1 - y2] + 1, out=row[y2:])
    return int(dp[S1, S2]) <= h

def triples(v, k, lam, shape, emin=2):
    n = k - lam
    Qt = sorted(quotient_types(shape))
    for p, e in sorted(primefac(n).items()):
        if e < emin: continue
        for h, m in Qt:
            if h == 1 or h % p == 0 or not self_conj(p, m): continue
            yield p, e, h, m, v // h

def w_sc(v, k, lam, shape):
    for p, e, h, m, c in triples(v, k, lam, shape):
        if p ** (e // 2) > 2 * c: return f"SC p={p} e={e} h={h} m={m} c={c}"
    return None

def w_a1(v, k, lam, shape):
    """A1 as stated: b = ceil(e/2) (p^(2b-1) | n); kill if p^b > 2c, or H = G (c = 1) with
    p^b = 2 and k < v."""
    for p, e, h, m, c in triples(v, k, lam, shape, emin=1):
        b = (e + 1) // 2
        if p ** b > 2 * c or (c == 1 and p ** b == 2 and k < v):
            return f"A1 p={p} e={e} b={b} h={h} m={m} c={c}"
    return None

def w_scpp(v, k, lam, shape):
    n = k - lam; s = s_of(v, k, lam); unsure = []
    for p, e, h, m, c in triples(v, k, lam, shape):
        q = p ** (e // 2); Q = n + lam * c
        V = V_of(c, h, s, q)
        if len(V) <= 1: return f"R1 p={p} j={e // 2} h={h} m={m} c={c} |V|={len(V)}"
        f = feas_milp(V, h, s, Q)
        if f is False: return f"R2 p={p} j={e // 2} h={h} m={m} c={c} |V|={len(V)}"
        if f is None: unsure.append((p, h))
    return f"unsure{unsure}".replace(' ', '') if unsure else None

def w_a2(v, k, lam, shape, maxvals=7):
    n = k - lam; s = s_of(v, k, lam); unsure = []
    for p, e, h, m, c in triples(v, k, lam, shape):
        q = p ** (e // 2); Q = n + lam * c
        V = V_of(c, h, s, q)
        if len(V) > maxvals: continue
        if not V: return f"A2 p={p} j={e // 2} h={h} m={m} c={c} |V|=0"
        f = feas_milp(V, h, s, Q, k, c)
        if f is False: return f"A2 p={p} j={e // 2} h={h} m={m} c={c} |V|={len(V)}"
        if f is None: unsure.append((p, h))
    return f"unsure{unsure}".replace(' ', '') if unsure else None
