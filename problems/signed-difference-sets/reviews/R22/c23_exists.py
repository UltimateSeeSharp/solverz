"""How hard is the C23/C14 test exercised on `exists` rows: rows reaching the box test, and any kill."""
import math, itertools
import sys, pathlib; sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from c23_check import rows, pfac, divs, sc_exp, box_ok
R = rows()
reach1 = reach2 = 0
for i, r in R.items():
    if r["status"] != "exists": continue
    v, k, lam, ms = r["v"], r["k"], r["lam"], r["ms"]
    n = k - lam; S = k + lam * (v - 1)
    if n == 0 or S < 0 or math.isqrt(S) ** 2 != S: continue
    s = math.isqrt(S); fn = pfac(abs(n)); seen = set(); r1 = r2 = False
    for ds in itertools.product(*[divs(m) for m in ms]):
        H, e = math.prod(ds), math.lcm(*ds)
        if H == 1 or (H, e) in seen: continue
        seen.add((H, e))
        good = [(p, a // 2) for p, a in fn.items() if a >= 2 and H % p and sc_exp(p, e)]
        cc = v // H; Q = k + lam * (cc - 1)
        for rsz in range(1, len(good) + 1):
            for sub in itertools.combinations(good, rsz):
                q = math.prod(p ** j for p, j in sub)
                if q > 20000: continue
                r1 = True; r2 = r2 or rsz >= 2
                if not any(box_ok(H, q, sp, Q, t, cc) for sp in (s, -s) for t in range(q)):
                    print("KILL of exists row", i, r, H, sub)
    reach1 += r1; reach2 += r2
print("exists rows reaching box test:", reach1, "with >=2 primes:", reach2)
