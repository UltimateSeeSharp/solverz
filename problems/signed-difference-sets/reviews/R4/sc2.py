# Full R2 ("SC++"), exact, no limit on |V|. Per Instance, per quotient type (h, m), per
# qualifying p (p^(2j) | n, p not dividing h, p self-conjugate mod m): all a_h = t mod q = p^j,
# t = s h^-1, |a_h| <= c; sum a = s; sum a^2 = n + lam c; not all equal. In y-space
# a = t0 + q y (t0 = least allowed value), z = y - floor(mean y): sum z = A, sum z^2 = B, at
# most h nonzero z (zeros fill), z in range. Kill if infeasible. Resumable: appends one line
# per Instance to the output; skips IDs already there. Usage:
#   python sc2.py <instances.csv> <out> <worker> <nworkers> [statuses]
import csv, sys, math, re, ctypes, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from indep import factor, selfconj, quotient_types
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
INF = 1 << 20

def min_count(A, B, zlo, zhi):
    """Least number of nonzero integers z in [zlo, zhi] with sum A and sum of squares B."""
    zs = [z for z in range(zlo, zhi + 1) if z != 0 and z * z <= B]
    off = B; cnt = np.full((2 * B + 1, B + 1), INF, dtype=np.int32); cnt[off, 0] = 0
    for tau in range(1, B + 1):
        col = cnt[:, tau]
        for z in zs:
            z2 = z * z
            if z2 > tau: continue
            src = cnt[:, tau - z2] + 1
            if z > 0: np.minimum(col[z:], src[:-z], out=col[z:])
            else: np.minimum(col[:z], src[-z:], out=col[:z])
    return int(cnt[off + A, B]) if -B <= A <= B else INF

def triple(v, k, lam, n, s, h, p, j):
    """None if a vector may exist on this quotient, else the reason it cannot."""
    q = p ** j; c = v // h; t = s * pow(h, -1, q) % q
    V = [x for x in range(-c, c + 1) if (x - t) % q == 0]
    if len(V) <= 1: return "R1"
    t0, R = V[0], len(V) - 1
    S1, r1 = divmod(s - h * t0, q); assert r1 == 0
    num = n + lam * c - h * t0 * t0 - 2 * t0 * q * S1
    if num % (q * q): return "R2div"
    S2 = num // (q * q)
    m = S1 // h; A = S1 - h * m; B = S2 - 2 * m * S1 + h * m * m
    if B <= 0 or B < A or (B - A) % 2: return "R2basic"   # B = 0 forces all equal
    if min_count(A, B, -m, R - m) > h: return "R2dp"
    return None

def verdict(v, k, lam, shape):
    n = k - lam
    if n <= 0: return None
    S = n + lam * v
    if S < 0 or math.isqrt(S) ** 2 != S: return "s-not-integer"
    s = math.isqrt(S)
    Q = sorted(quotient_types(shape))
    for p, e in factor(n).items():
        j = e // 2
        if j == 0: continue
        for h, m in Q:
            if h == 1 or h % p == 0 or not selfconj(p, m): continue
            why = triple(v, k, lam, n, s, h, p, j)
            if why: return f"{why} p={p} j={j} h={h} m={m} c={v // h}"
    return None

if __name__ == "__main__":
    ctypes.windll.kernel32.SetPriorityClass(ctypes.windll.kernel32.GetCurrentProcess(), 0x4000)  # below normal
    src, out, w, nw = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    statuses = set(sys.argv[5].split(",")) if len(sys.argv) > 5 else {"open", "exists"}
    done = {l.split()[0] for l in open(out, encoding="utf-8")} if os.path.exists(out) else set()
    rows = [r for r in csv.DictReader(open(src, encoding="utf-8")) if r["status"] in statuses]
    with open(out, "a", encoding="utf-8") as f:
        for i, r in enumerate(rows):
            if i % nw != w or r["id"] in done: continue
            mm = KEY.fullmatch(r["key"]); v, k, lam = map(int, mm.groups()[:3])
            shape = [int(x) for x in mm.group(4).split(",")]
            f.write(f"{r['id']} {r['status']} {r['key']} {verdict(v, k, lam, shape) or 'open'}\n"); f.flush()
