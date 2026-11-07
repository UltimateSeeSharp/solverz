"""Does C14's box test with q already fail whenever 2c < q (C23's 'C5 with q')? Scan all rows/quotients."""
import sys, pathlib, math, itertools; sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from c23_check import rows, pfac, divs, sc_exp, box_ok
R = rows(); cases = passes = 0; ex = None
for i, r in R.items():
    v, k, lam, ms = r["v"], r["k"], r["lam"], r["ms"]; n = k - lam; S = k + lam * (v - 1)
    if n == 0 or S < 0 or math.isqrt(S) ** 2 != S: continue
    s = math.isqrt(S); fn = pfac(abs(n)); seen = set()
    for ds in itertools.product(*[divs(m) for m in ms]):
        H, e = math.prod(ds), math.lcm(*ds)
        if H == 1 or (H, e) in seen: continue
        seen.add((H, e))
        good = [p ** (a // 2) for p, a in fn.items() if a >= 2 and H % p and sc_exp(p, e)]
        q = math.prod(good); c = v // H
        if len(good) >= 2 and 2 * c < q <= 20000:
            cases += 1
            Q = k + lam * (c - 1)
            if any(box_ok(H, q, sp, Q, t, c) for sp in (s, -s) for t in range(q)):
                passes += 1; ex = ex or (i, H, q, c)
print("quotients with >=2 primes and 2c<q:", cases, "box test passes on:", passes, ex)
