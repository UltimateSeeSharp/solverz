"""Independent C26 check: for an SDS D on G = Z_m1 x ... x Z_mt, every (or sampled) surjection
phi: G -> H = Z_N x Z_d1 x ... (N = 2^j, d odd), checks (a) 2 | Y(h+u) - Y(h), u = (N/2, 0, ..),
and (b) 8 | 2 s' - (k + lam (2c - 1)) with the actual s' = sum D. Reports separately quotients whose K is
NOT 2-self-conjugate (negative control)."""
import itertools, math, random
import numpy as np

def selfconj2(d):
    if d == 1: return True
    x = 2 % d
    for _ in range(d):
        if x == d - 1: return True
        x = x * 2 % d
    return False

def elements(ms):
    return list(itertools.product(*[range(m) for m in ms]))

def hom_choices(ms, N):
    """All homs Z_m -> Z_N per coordinate: x -> b x with N | b m."""
    return [[b for b in range(N) if (b * m) % N == 0] for m in ms]

def is_sds(ms, D):
    """D: dict elem -> +-1. Returns (k, lam) or None."""
    E = elements(ms); idx = {e: i for i, e in enumerate(E)}
    v = len(E); vec = np.zeros(v, dtype=np.int64)
    for e, s in D.items(): vec[idx[e]] = s
    lam = None
    for g in E:
        if all(x == 0 for x in g): continue
        sh = np.array([idx[tuple((a + b) % m for a, b, m in zip(e, g, ms))] for e in E])
        a = int((vec * vec[sh]).sum())
        if lam is None: lam = a
        elif a != lam: return None
    return len(D), lam

def check_quotient(ms, D, Ns, forms, k, lam):
    """forms: list (one per H-coordinate) of coefficient tuples. Ns: H moduli, Ns[0] = 2^j.
    Returns None if not surjective, else (ok_a, ok_b, c)."""
    img = {}
    for e, s in D.items():
        h = tuple(sum(b * x for b, x in zip(f, e)) % n for f, n in zip(forms, Ns))
        img[h] = img.get(h, 0) + s
    # surjectivity: image of generators spans H; test by image of all of G (small) or generator closure
    gens = []
    for t in range(len(ms)):
        e = tuple(1 if q == t else 0 for q in range(len(ms)))
        gens.append(tuple(sum(b * x for b, x in zip(f, e)) % n for f, n in zip(forms, Ns)))
    H = 1
    for n in Ns: H *= n
    seen = {tuple(0 for _ in Ns)}; frontier = list(seen)
    while frontier:
        nxt = []
        for h in frontier:
            for g in gens:
                y = tuple((a + b) % n for a, b, n in zip(h, g, Ns))
                if y not in seen: seen.add(y); nxt.append(y)
        frontier = nxt
    if len(seen) != H: return None
    v = math.prod(ms); c = v // H
    N = Ns[0]
    ok_a = True
    for h in itertools.product(*[range(n) for n in Ns]):
        hu = ((h[0] + N // 2) % N,) + h[1:]
        if (img.get(h, 0) - img.get(hu, 0)) % 2: ok_a = False; break
    s1 = sum(D.values())
    ok_b = (2 * s1 - (k + lam * (2 * c - 1))) % 8 == 0
    return ok_a, ok_b, c

def odd_part(m):
    while m % 2 == 0: m //= 2
    return m

def quotient_shapes(ms):
    """Shapes (N, [d...]) with N = 2^j <= max 2-part, K = prod C_d, d odd, d | exp(odd part); up to 2 K-factors."""
    J = max((m & -m) for m in ms)
    ex = math.lcm(*[odd_part(m) for m in ms])
    ods = [d for d in range(3, ex + 1, 2) if ex % d == 0]
    shapes = []
    N = 2
    while N <= J:
        shapes.append((N, []))
        for d in ods: shapes.append((N, [d]))
        for d1, d2 in itertools.combinations_with_replacement(ods, 2): shapes.append((N, [d1, d2]))
        N *= 2
    return shapes

def run_set(ms, D, k, lam, exhaustive_limit=20000, samples=60, rng=random.Random(1)):
    """Returns list of (shape, selfconj, ok_a, ok_b, c) for surjective quotients found."""
    res = []
    for N, ds in quotient_shapes(ms):
        Ns = [N] + ds
        choices = [list(itertools.product(*hom_choices(ms, n))) for n in Ns]
        total = math.prod(len(ch) for ch in choices)
        sc = selfconj2(math.lcm(1, *ds))
        if total <= exhaustive_limit:
            it = itertools.product(*choices)
        else:
            it = (tuple(rng.choice(ch) for ch in choices) for _ in range(samples))
        for forms in it:
            r = check_quotient(ms, D, Ns, forms, k, lam)
            if r is None: continue
            res.append(((N, tuple(ds)), sc, r[0], r[1], r[2], forms))
    return res
