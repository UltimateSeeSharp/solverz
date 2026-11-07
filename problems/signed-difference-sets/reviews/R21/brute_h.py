# Every integer vector a on a small p-group H with constant off-zero autocorrelation (aa^(-1) = n + mu H, n > 0):
# check C22's conclusion with t = log_p |H|, e = v_p(n), s' = sum(a); and for p = 2 that n is a square.
import sys, os, itertools, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cyc import val

def group(orders):
    G = list(itertools.product(*[range(o) for o in orders]))
    idx = {g: i for i, g in enumerate(G)}
    shifts = []
    for g in G[1:]:
        shifts.append([idx[tuple((x + y) % o for x, y, o in zip(h, g, orders))] for h in G])
    return G, shifts

def run(orders, B, p):
    G, shifts = group(orders)
    N = len(G); t = val(N, p)
    rng = range(-B, B + 1)
    found = 0; viol = []; stats = {}
    s1, s2 = shifts[0], shifts[1:]
    for a in itertools.product(rng, repeat=N):
        # negation symmetry: first nonzero entry positive
        fz = next((x for x in a if x), 0)
        if fz <= 0:
            continue
        c = 0
        for i in range(N):
            c += a[i] * a[s1[i]]
        ok = True
        for sh in s2:
            d = 0
            for i in range(N):
                d += a[i] * a[sh[i]]
            if d != c:
                ok = False; break
        if not ok:
            continue
        mu = c
        n = sum(x * x for x in a) - mu
        if n <= 0:
            continue
        sp = sum(a)
        assert sp * sp == n + mu * N
        found += 1
        e = val(n, p)
        if p == 2:
            m = math.isqrt(n)
            if m * m != n:
                viol.append(("nsq", a, n, mu)); continue
            w = val(m, 2)
            okc = min(val(sp, 2), t) == min(w, t)
            key = (min(val(sp, 2), 9), w)
        else:
            okc = val(sp, p) >= min(t, (e + 1) // 2)
            key = (min(val(sp, p), 9), e)
        stats[key] = stats.get(key, 0) + 1
        if not okc:
            viol.append(("C22", a, n, mu, sp))
    return found, viol, stats

if __name__ == "__main__":
    cases = [([2], 15, 2), ([3], 12, 3), ([4], 7, 2), ([2, 2], 7, 2), ([5], 6, 5), ([7], 3, 7),
             ([8], 3, 2), ([2, 4], 3, 2), ([2, 2, 2], 3, 2), ([9], 2, 3), ([3, 3], 2, 3)]
    if len(sys.argv) > 1:
        cases = cases[int(sys.argv[1]):int(sys.argv[2])]
    for orders, B, p in cases:
        f, v, st = run(orders, B, p)
        print(orders, "range", B, "p", p, "vectors", f, "violations", len(v), v[:3], flush=True)
        print("   (v_p(s') capped 9, e or w) counts:", dict(sorted(st.items())), flush=True)
