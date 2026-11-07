# Every known SDS (objects/, E10 found, E4/E7 yes, B4's order-64 sets): verify it, then on quotients
# H = C_{p^j} x K test C21's lemma (1 - g_P) Y = 0 mod p^b and that the rule p^b > 2c never fires.
import os, re, math, random, itertools, glob, sys, ast, collections
W = "problems/signed-difference-sets/"
random.seed(1)
def vp(x, p):
    c = 0
    while x % p == 0: x //= p; c += 1
    return c
def factorize(n):
    f = {}; d = 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def sc(p, m):
    return m == 1 or any((pow(p, i, m) + 1) % m == 0 for i in range(1, m + 1))
def sc_orders(p, m):  # weaker: p self-conjugate mod every divisor d > 1 of m separately
    return all(sc(p, d) for d in range(2, m + 1) if m % d == 0)

def sets():
    for f in sorted(glob.glob(W + "objects/O*.txt")):
        L = open(f).read().split('\n'); m = re.match(r"(\S+) \((-?\d+),(-?\d+),(-?\d+)\)", L[0])
        fs = [int(x) for x in m[1].replace('C', '').split('x')]; k, l = int(m[3]), int(m[4])
        D = {}
        for line in L[1:]:
            t = line.split()
            if not t: continue
            D[tuple(int(x) for x in t[:-1])] = 1 if t[-1] == '+' else -1
        yield os.path.basename(f), fs, k, l, D
    for src in ("scratch/e10.out", "scratch/e11.out", "scratch/r4.out", "scratch/e7.out"):
        try: lines = open(W + src).read().split('\n')
        except FileNotFoundError: continue
        for line in lines:
            m = re.match(r"(N\d+) SDS\((\d+),(-?\d+),(-?\d+),\[([\d,]+)\]\) (found|yes) (.*)", line)
            if not m: continue
            fs = [int(x) for x in m[5].split(',')]; D = {}
            for tok in m[7].split():
                mm = re.fullmatch(r"([\d.]+)([+-])", tok)
                if mm: D[tuple(int(x) for x in mm[1].split('.'))] = 1 if mm[2] == '+' else -1
            yield src + ":" + m[1], fs, int(m[3]), int(m[4]), D
    for i, line in enumerate(open(W + "scratch/ideator/r2/f1_64_sets.txt")):
        m = re.match(r"(\[[\d, ]+\]) \S+ k=(\d+) s=(-?\d+) lam=\{(-?\d+)\} plus=(\[.*?\]) minus=(\[.*?\])", line)
        if not m: print("unparsed f1 line", i); continue
        fs = ast.literal_eval(m[1]); D = {t: 1 for t in ast.literal_eval(m[5])}
        for t in ast.literal_eval(m[6]): D[t] = -1
        yield f"f1_64:{i}", fs, int(m[2]), int(m[4]), D

def verify(fs, k, l, D):
    if len(D) != k: return False
    els = list(itertools.product(*[range(m) for m in fs])); items = list(D.items())
    for g in els:
        if not any(g): continue
        s = 0
        for x, dx in items:
            y = tuple((a + b) % m for a, b, m in zip(x, g, fs))
            s += dx * D.get(y, 0)
        if s != l: return False
    return True

def kshapes(fs, p):
    """All p'-quotients K of G as lists of prime-power cyclic orders."""
    prim = collections.defaultdict(list)
    for m in fs:
        for q, a in factorize(m).items():
            if q != p: prim[q].append(a)
    per = []
    for q, gs in prim.items():
        gs = sorted(gs, reverse=True); opts = []
        def rec(i, prev, cur):
            if i == len(gs): opts.append([q ** a for a in cur if a]); return
            for a in range(min(prev, gs[i]), -1, -1): rec(i + 1, a, cur + [a])
        rec(0, 99, []); per.append(opts)
    for combo in itertools.product(*per): yield [x for part in combo for x in part]

def closure_size(gens, hs):
    seen = {tuple(0 for _ in hs)}; frontier = list(seen)
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = tuple((a + b) % h for a, b, h in zip(x, g, hs))
                if y not in seen: seen.add(y); nf.append(y)
        frontier = nf
    return len(seen)

def homs(fs, hs, nrand):
    """Coordinate-style surjections when possible, plus random surjective homs G -> prod C_h."""
    out = []
    allowed = [[[a for a in range(h) if (m * a) % h == 0] for h in hs] for m in fs]
    tries = 0
    while len(out) < nrand and tries < 50 * nrand:
        tries += 1
        A = [tuple(random.choice(allowed[i][l]) for l in range(len(hs))) for i in range(len(fs))]
        if closure_size(A, hs) == math.prod(hs): out.append(A)
    return out

stats = collections.Counter(); viol = []; fired = []; ctrl = collections.Counter()
for name, fs, k, l, D in sets():
    v = math.prod(fs); n = k - l
    ok = verify(fs, k, l, D) if v <= 4096 else None
    stats['sets'] += 1; stats['verified' if ok else 'NOT verified'] += 1
    if not ok: print("not an SDS?", name, fs, k, l); continue
    for p in factorize(n) if n > 0 else []:
        e = vp(n, p); b = e // 2
        jmax = max(vp(m, p) for m in fs)
        if b == 0 or jmax == 0: continue
        for j in range(1, jmax + 1):
            for K in kshapes(fs, p):
                expK = math.lcm(*K) if K else 1
                cls = 'claim' if sc(p, expK) else ('orders' if sc_orders(p, expK) else 'control')
                hs = [p ** j] + K; Hs = math.prod(hs); c = v // Hs
                if Hs > 3000: continue
                for A in homs(fs, hs, 6):
                    Y = collections.Counter()
                    for x, dx in D.items():
                        Y[tuple(sum(xi * a[t] for xi, a in zip(x, A)) % hs[t] for t in range(len(hs)))] += dx
                    gP = (p ** (j - 1),) + (0,) * len(K)
                    bad = any((Y[h] - Y[tuple((a - g) % m for a, g, m in zip(h, gP, hs))]) % p ** b
                              for h in itertools.product(*[range(m) for m in hs]))
                    stats[(cls, 'tests')] += 1
                    if cls == 'claim': stats[('claim', p, 'b', b, 'K>1' if K else 'K=1')] += 1
                    if bad: stats[(cls, 'violations')] += 1
                    if bad and cls == 'claim': viol.append((name, p, j, K))
                    if cls == 'claim' and p ** b > 2 * c: fired.append((name, p, j, K, c))
print(dict(stats)); print("claim violations:", viol[:10]); print("rule fired on a real set:", fired[:10])
