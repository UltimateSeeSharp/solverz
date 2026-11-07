# Stress C22 where e/2 and t are close: group-ring products of solutions are solutions
# ((n1 + mu1 H)(n2 + mu2 H) = n1 n2 + (n1 mu2 + n2 mu1 + mu1 mu2 |H|) H), plus shifts a + cH.
import sys, os, itertools, math, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cyc import val
from brute_h import group

def solutions(orders, B):
    G, shifts = group(orders); N = len(G); out = []
    for a in itertools.product(range(-B, B + 1), repeat=N):
        if next((x for x in a if x), 0) <= 0: continue
        c = sum(a[i] * a[shifts[0][i]] for i in range(N))
        if all(sum(a[i] * a[sh[i]] for i in range(N)) == c for sh in shifts[1:]):
            if sum(x * x for x in a) - c > 0: out.append(a)
    return out

def tools(orders):
    G = list(itertools.product(*[range(o) for o in orders])); idx = {g: i for i, g in enumerate(G)}
    addt = [[idx[tuple((x + y) % o for x, y, o in zip(g, h, orders))] for h in G] for g in G]
    neg = [idx[tuple((-x) % o for x, o in zip(g, orders))] for g in G]
    return G, addt, neg

def mulvec(a, b, addt):
    N = len(a); out = [0] * N
    for i in range(N):
        if a[i]:
            r = addt[i]
            for j in range(N):
                if b[j]: out[r[j]] += a[i] * b[j]
    return out

def check(a, addt, neg, p, t, stats, viol):
    N = len(a)
    ainv = [a[neg[i]] for i in range(N)]
    c = mulvec(a, ainv, addt)
    mu = c[1]
    assert all(x == mu for x in c[1:]), "product not constant"
    n = c[0] - mu
    if n <= 0: return
    sp = sum(a)
    e = val(n, p)
    if p == 2:
        m = math.isqrt(n)
        if m * m != n: viol.append(("nsq", a)); return
        w = val(m, 2); ok = min(val(sp, 2), t) == min(w, t); key = (min(w, 9), min(val(sp, 2), 9))
    else:
        ok = val(sp, p) >= min(t, (e + 1) // 2); key = (e, min(val(sp, p), 9))
    stats[key] += 1
    if not ok: viol.append(("C22", a, n, mu, sp))

if __name__ == "__main__":
    random.seed(1)
    cases = [([4], 4, 2), ([2, 2], 4, 2), ([8], 2, 2), ([2, 4], 2, 2), ([2, 2, 2], 2, 2), ([9], 1, 3), ([3, 3], 1, 3),
             ([5], 3, 5), ([7], 2, 7)]
    for orders, B, p in cases:
        base = solutions(orders, B)
        G, addt, neg = tools(orders); N = len(G); t = val(N, p)
        stats = collections.Counter(); viol = []
        pool = [list(a) for a in base]
        prods = []
        for i in range(len(pool)):
            for j in range(i, len(pool)):
                prods.append(mulvec(pool[i], pool[j], addt))
        trip = [mulvec(random.choice(prods), random.choice(pool), addt) for _ in range(20000)]
        quad = [mulvec(random.choice(prods), random.choice(prods), addt) for _ in range(20000)]
        allv = pool + prods + trip + quad
        for a in allv:
            for cc in (-2, -1, 0, 1, 3):
                check([x + cc for x in a], addt, neg, p, t, stats, viol)
        print(orders, "p", p, "t", t, "base", len(base), "tested", sum(stats.values()), "violations", len(viol), viol[:2], flush=True)
        print("   (e or w, v_p(s') capped 9):", dict(sorted(stats.items())), flush=True)
