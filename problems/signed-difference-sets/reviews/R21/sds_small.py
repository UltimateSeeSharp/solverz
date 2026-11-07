# All SDS on every abelian group of order <= 12 (exhaustive over {-1,0,1}^G, negation-normalized); C22 for every p | v.
import sys, os, itertools, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cyc import val
from brute_h import group
GROUPS = [[2], [3], [4], [2, 2], [5], [6], [7], [8], [2, 4], [2, 2, 2], [9], [3, 3], [10], [11], [12], [2, 6]]
def primes(x): return [p for p in range(2, x + 1) if x % p == 0 and all(p % d for d in range(2, p))]
tot = 0; bad = []; params = set()
for orders in GROUPS:
    G, shifts = group(orders); N = len(G); cnt = 0
    for a in itertools.product((-1, 0, 1), repeat=N):
        if next((x for x in a if x), 0) <= 0: continue
        c = sum(a[i] * a[shifts[0][i]] for i in range(N))
        if not all(sum(a[i] * a[sh[i]] for i in range(N)) == c for sh in shifts[1:]): continue
        k = sum(1 for x in a if x); lam = c; n = k - lam
        if n <= 0: continue
        cnt += 1; s = abs(sum(a)); params.add((N, k, lam, tuple(orders)))
        for p in primes(N):
            t = val(N, p); e = val(n, p)
            if p == 2:
                m = math.isqrt(n)
                if m * m != n: bad.append((orders, a, "nsq")); continue
                if min(val(s, 2), t) != min(val(m, 2), t): bad.append((orders, a, "eq"))
            elif val(s, p) < min(t, (e + 1) // 2): bad.append((orders, a, "div"))
    tot += cnt
    print(orders, "SDS (up to sign)", cnt, flush=True)
print("total", tot, "violations", bad[:5], len(bad))
print("parameter sets realized:", sorted(params))
