# Independent kill test: exhaustively search integer vectors a on every group H of order p^t (the Sylow quotient
# of a hit row) with sum(a) = s, sum(a^2) = n + mu, |a_h| <= v/p^t, and constant autocorrelation mu off zero.
# C22 says none exist on hit rows. Positive controls: rows of known SDS (must find their coset-sum vectors).
import sys, os, math, itertools, csv, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from brute_h import group
GROUPS = {4: [[4], [2, 2]], 8: [[8], [2, 4], [2, 2, 2]], 9: [[9], [3, 3]]}

def vectors(N, Q, S, cap):
    """All integer vectors of length N, max entry at index 0, sum S, sum of squares Q, |entries| <= cap."""
    out = []
    a = [0] * N
    def rec(i, r, q, top):
        L = N - i
        if L == 0:
            if r == 0 and q == 0: out.append(tuple(a))
            return
        if q < 0 or r * r > L * q or (q - r) % 2 or r > L * top: return
        hi = min(top, math.isqrt(q)); lo = -min(cap, math.isqrt(q))
        for x in range(lo, hi + 1):
            a[i] = x; rec(i + 1, r - x, q - x * x, top)
    for x0 in range(-min(cap, math.isqrt(Q)), min(cap, math.isqrt(Q)) + 1):
        a[0] = x0; rec(1, S - x0, Q - x0 * x0, x0)
    return out

def search(N, n, mu, s, cap):
    Q = n + mu; found = []
    vs = vectors(N, Q, s, cap)
    for orders in GROUPS[N]:
        G, shifts = group(orders)
        for a in vs:
            if all(sum(a[i] * a[sh[i]] for i in range(N)) == mu for sh in shifts):
                found.append((orders, a))
    return len(vs), found

if __name__ == "__main__":
    P = "problems/signed-difference-sets/"
    # positive controls (known SDS): (36,11,2) O21/O22 on 9 and 4; (45,37,1) O23 on 9; (27,10,1) O7 on 9 (Sylow is G, skip)
    controls = [("O21 (36,11,2) p=3", 9, 9, 8, 9, 4), ("O21 (36,11,2) p=2", 4, 9, 18, 9, 9),
                ("O23 (45,37,1) p=3", 9, 36, 5, 9, 5), ("O25 (63,47,11) p=3", 9, 36, 77, 27, 7)]
    for name, N, n, mu, s, cap in controls:
        cnt, f = search(N, n, mu, s, cap)
        print("CONTROL", name, "candidates", cnt, "found", len(f), f[:1], flush=True)
    KEY = re.compile(r"SDS\((-?\d+),(-?\d+),(-?\d+),\[([\d,]+)\]\)")
    hits = {l.split()[0]: l.split()[1:] for l in open(P + "reviews/R21/my_hits.txt")}
    def val(x, p):
        c = 0
        while x % p == 0: x //= p; c += 1
        return c
    todo = {}
    for r in csv.DictReader(open(P + "instances.csv", newline="")):
        if r["id"] not in hits or r["status"] != "open": continue
        m = KEY.match(r["key"]); v, k, l = int(m[1]), int(m[2]), int(m[3])
        for tag in hits[r["id"]]:
            p = int(re.match(r"\d+", tag)[0]); t = val(v, p); N = p ** t
            if N in GROUPS:
                key = (N, k - l, l * v // N, math.isqrt(k + l * (v - 1)), v // N)
                todo.setdefault(key, []).append(r["id"])
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10**9
    tot = 0; bad = []
    for key in sorted(todo, key=lambda x: x[1] + x[2])[:limit]:
        N, n, mu, s, cap = key
        cnt, f = search(N, n, mu, s, cap)
        tot += 1
        print(key, todo[key][:3], "candidates", cnt, "found", len(f), f[:1], flush=True)
        if f: bad.append((key, f[:1]))
    print("parameter classes searched", tot, "of", len(todo), "with a vector:", bad)
