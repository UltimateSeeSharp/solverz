# Extra real objects with K != 1 and b >= 2: tensor products of circulant weighing matrices (lambda = 0 is closed
# under products). Check C21's lemma on every quotient C_{p^j} x K with K a coordinate p'-quotient, all surjections
# of the C_{p^j} part from each factor, and the rule never firing.
import itertools, math, collections
def vp(x, p):
    c = 0
    while x % p == 0: x //= p; c += 1
    return c
def sc(p, m): return m == 1 or any((pow(p, i, m) + 1) % m == 0 for i in range(1, m + 1))
def cw(v, w):  # all CW(v, w) in C_v, w = weight, by brute force (small v)
    out = []
    for D in itertools.product((-1, 0, 1), repeat=v):
        if sum(d * d for d in D) != w or D[0] == 0: continue
        if all(sum(D[i] * D[(i + g) % v] for i in range(v)) == 0 for g in range(1, v)): out.append(D)
    return out
base = {4: cw(4, 4)[0], 6: cw(6, 4)[0], 7: cw(7, 4)[0], 8: cw(8, 4)[0]}
print({v: D for v, D in base.items()})
def tensor(vs):
    D = {}
    for xs in itertools.product(*[range(v) for v in vs]):
        s = math.prod(base[v][x] for v, x in zip(vs, xs))
        if s: D[xs] = s
    return D
def check(vs):
    D = tensor(vs); v = math.prod(vs); n = 4 ** len(vs)
    # verify SDS with lambda = 0
    for g in itertools.product(*[range(m) for m in vs]):
        if any(g):
            s = sum(dx * D.get(tuple((a + b) % m for a, b, m in zip(x, g, vs)), 0) for x, dx in D.items())
            assert s == 0
    res = collections.Counter(); p = 2; b = vp(n, p) // 2
    for i, m in enumerate(vs):  # C_{2^j} from factor i (coordinate projection)
        for j in range(1, vp(m, 2) + 1):
            odd = [x // 2 ** vp(x, 2) for x in vs]
            for ds in itertools.product(*[[d for d in range(1, o + 1) if o % d == 0] for o in odd]):
                expK = math.lcm(*ds)
                if not sc(2, expK): continue
                q = 2 ** j; Ksz = math.prod(ds); c = v // (q * Ksz)
                Y = collections.Counter()
                for x, dx in D.items(): Y[(x[i] % q,) + tuple(xx % d for xx, d in zip(x, ds))] += dx
                bad = any((Y[h] - Y[((h[0] - q // 2) % q,) + h[1:]]) % 2 ** b
                          for h in itertools.product(range(q), *[range(d) for d in ds]))
                res['tests'] += 1; res['K>1' if Ksz > 1 else 'K=1'] += 1
                if bad: res['VIOLATION'] += 1; print("violation", vs, i, j, ds)
                if 2 ** b > 2 * c: res['RULE FIRED'] += 1; print("rule fired", vs, i, j, ds, c)
    print("CW(%d,%d) in %s: b=%d" % (v, n, "x".join("C%d" % m for m in vs), b), dict(res), flush=True)
for vs in [(6, 6), (4, 6), (6, 7), (4, 4, 6), (6, 6, 6), (6, 8), (4, 6, 7)]:
    check(vs)
