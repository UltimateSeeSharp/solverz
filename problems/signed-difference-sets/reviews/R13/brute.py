"""Independent brute force of C9/C10 (Lean Multiplier.lean) on small abelian groups.

Vectors a in R^G (R = {-1,0,1} for SDS, {-r..r} for integer vectors) whose autocorrelation is
n*[g=0] + mu. Keep n squarefree (n=1 included; n<=0 skipped, logged), gcd(v, n) = 1. T = { t mod e :
gcd(t, e) = 1, for every prime p | n some f >= 0 with t = p^f mod e } (Lean: Nat.Coprime t v and
t.x = p^f.x on G). Claim: some translate c has a(t x + c) = a(x + c) for all t in T, x in G.
Usage: brute.py R maxv [shapes...]   (shape like 2x6)
"""
import sys, math, itertools, os
import numpy as np

def sqfree(n):
    if n < 1: return False
    p = 2
    while p * p <= n:
        if n % (p * p) == 0: return False
        p += 1
    return True

def primes(n):
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0: n //= p
        p += 1
    if n > 1: out.append(n)
    return out

def groups(maxv):
    # all abelian groups of order <= maxv as invariant-factor shapes m1 | m2 | ...
    def inv(v, minf=2, last=None):
        # shapes as lists with each dividing next
        if v == 1: yield []; return
        for m in range(2, v + 1):
            if v % m: continue
            for rest in inv(v // m):
                if rest and rest[0] % m: continue
                yield [m] + rest
    out = [[1]]
    for v in range(2, maxv + 1):
        for s in inv(v): out.append(s)
    return out

class G:
    def __init__(self, shape):
        self.shape = shape
        self.v = math.prod(shape)
        self.e = math.lcm(*shape)
        self.elts = list(itertools.product(*[range(m) for m in shape]))
        self.idx = {x: i for i, x in enumerate(self.elts)}
        v = self.v
        self.add = np.array([[self.idx[tuple((a + b) % m for a, b, m in zip(x, y, shape))]
                              for y in self.elts] for x in self.elts])
    def scale(self, t):
        return np.array([self.idx[tuple((t * a) % m for a, m in zip(x, self.shape))] for x in self.elts])

def T_set(g, n):
    e = g.e
    ps = primes(n)
    out = []
    for t in range(e):
        if math.gcd(t, e) != 1: continue
        ok = True
        for p in ps:
            if not any(pow(p, f, e) == t % e for f in range(e + 1)):
                ok = False; break
        if ok: out.append(t)
    return out

def all_units(g):
    return [t for t in range(g.e) if math.gcd(t, g.e) == 1]

def fixed_translate(g, a, T):
    """Return c with a(t x + c) = a(x + c) for all t in T, or None."""
    scales = [g.scale(t) for t in T]
    for c in range(g.v):
        sh = g.add[:, c]            # x -> x + c
        b = a[sh]
        if all(np.array_equal(b[s], b) for s in scales):
            return c
    return None

def search(g, R, chunk=1 << 21):
    v = g.v
    base = 2 * R + 1
    total = base ** v
    pw = base ** np.arange(v, dtype=np.int64)
    found = []
    for i0 in range(0, total, chunk):
        idx = np.arange(i0, min(total, i0 + chunk), dtype=np.int64)
        A = ((idx[:, None] // pw[None, :]) % base - R).astype(np.int32)
        if v == 1:
            for row in A: found.append(row.copy())
            continue
        # progressive filter: all nonzero shifts give the same value
        lam = (A * A[:, g.add[:, 1]]).sum(1)
        keep = np.ones(len(A), bool)
        for s in range(2, v):
            keep &= (A * A[:, g.add[:, s]]).sum(1) == lam
            if s % 3 == 0:
                A, lam, keep = A[keep], lam[keep], np.ones(keep.sum(), bool)
        A = A[keep]
        for row in A: found.append(row.copy())
    return found

def main():
    R = int(sys.argv[1]); maxv = int(sys.argv[2])
    shapes = [list(map(int, s.split('x'))) for s in sys.argv[3:]] or groups(maxv)
    stats = dict(vec=0, applies=0, ok=0, fail=0, nonpos=0, units_fail=0, nonsqf_ok=0, nonsqf_fail=0)
    for shape in shapes:
        g = G(shape)
        if g.v > maxv: continue
        vecs = search(g, R)
        loc = dict(applies=0, fail=0, n1=0, units_fail=0, nonsqf=0, nonsqf_fail=0, Tmax=0)
        for a in vecs:
            stats['vec'] += 1
            ac0 = int((a * a).sum())
            mu = int((a * a[g.add[:, 1]]).sum()) if g.v > 1 else 0
            n = ac0 - mu
            if g.v == 1:
                n = None
            if n is None or n < 1:
                stats['nonpos'] += 1; continue
            if math.gcd(g.v, n) != 1: continue
            s = int(a.sum()); assert s * s == n + mu * g.v
            T = T_set(g, n)
            if not sqfree(n):
                loc['nonsqf'] += 1
                if fixed_translate(g, a, T) is None:
                    loc['nonsqf_fail'] += 1; stats['nonsqf_fail'] += 1
                    print('NONSQF FAIL', shape, n, mu, a.tolist(), flush=True)
                else: stats['nonsqf_ok'] += 1
                continue
            loc['applies'] += 1; stats['applies'] += 1
            loc['Tmax'] = max(loc['Tmax'], len(T))
            if n == 1: loc['n1'] += 1
            c = fixed_translate(g, a, T)
            if c is None:
                loc['fail'] += 1; stats['fail'] += 1
                print('COUNTEREXAMPLE', shape, 'n', n, 'mu', mu, 'T', T, a.tolist(), flush=True)
            else:
                stats['ok'] += 1
            # validation: all units must fail sometimes for n > 1
            if n > 1 and fixed_translate(g, a, all_units(g)) is None:
                loc['units_fail'] += 1; stats['units_fail'] += 1
        print('group', shape, 'v', g.v, 'vectors', len(vecs), loc, flush=True)
    print('TOTAL', stats, flush=True)

if __name__ == '__main__':
    main()
