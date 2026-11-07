# The lemma's algebraic core, in A = Z[H]/(P) directly: every alpha with coordinates in [-r, r] on the Z-basis
# {g^t k : t < phi, k in K} of A and alpha*alphabar = n in A (n = 0 included): check alpha in p^b A
# (all coordinates = 0 mod p^b; n = 0: alpha = 0). Wider than constant autocorrelation (only "mod P" needed).
import itertools, math, sys, collections
def vp(x, p):
    c = 0
    while x % p == 0: x //= p; c += 1
    return c
def run(p, j, K, r, label):
    q = p ** j; phi = q - q // p; hs = [q] + K
    kel = list(itertools.product(*[range(m) for m in K])); nk = len(kel); kidx = {e: i for i, e in enumerate(kel)}
    kadd = [[kidx[tuple((a + b) % m for a, b, m in zip(x, y, K))] for y in kel] for x in kel]
    kneg = [kidx[tuple((-a) % m for a, m in zip(x, K))] for x in kel]
    dim = phi * nk; s = q // p
    cnt = collections.Counter(); bad = []
    for alpha in itertools.product(range(-r, r + 1), repeat=dim):
        nz = [(i // nk, i % nk, a) for i, a in enumerate(alpha) if a]
        Z = [0] * (q * nk)
        for t1, k1, a1 in nz:
            for t2, k2, a2 in nz:
                Z[((t1 - t2) % q) * nk + kadd[k1][kneg[k2]]] += a1 * a2
        # reduce mod Phi_q(x) = sum_{u<p} x^{u s}: x^{(p-1)s + w} = -sum_{u<p-1} x^{u s + w}
        for w in range(s):
            for kk in range(nk):
                c = Z[((p - 1) * s + w) * nk + kk]
                if c:
                    for u in range(p - 1): Z[(u * s + w) * nk + kk] -= c
        n = Z[0]
        if any(Z[i] for i in range(1, phi * nk)): continue
        if n == 0:
            cnt['n=0'] += 1
            if any(alpha): bad.append((0, alpha))
            continue
        e = vp(n, p); b = e // 2
        if b == 0: cnt['e<2'] += 1; continue
        cnt[('b', b)] += 1
        if any(a % p ** b for a in alpha): bad.append((n, alpha))
    print(label, "p", p, "j", j, "K", K, "dim", dim, "r", r, dict(cnt), "violations", len(bad), bad[:3], flush=True)
cases = {
 'a': [(2, 1, [3], 8, 'claim'), (2, 1, [5], 3, 'claim'), (2, 1, [9], 1, 'claim'), (2, 1, [3, 3], 1, 'claim'),
       (2, 1, [11], 1, 'claim'), (2, 1, [13], 1, 'claim'), (2, 1, [7], 2, 'CONTROL'), (2, 2, [3], 3, 'claim'),
       (2, 3, [], 6, 'claim K=1'), (2, 2, [5], 1, 'claim'), (2, 3, [3], 1, 'claim'), (2, 2, [], 20, 'claim K=1')],
 'b': [(3, 1, [2], 6, 'claim'), (3, 1, [4], 2, 'claim'), (3, 1, [2, 2], 2, 'claim'), 
       (3, 1, [5], 1, 'claim'), (3, 2, [], 4, 'claim K=1'), (3, 1, [7], 1, 'claim'), (5, 1, [], 8, 'claim K=1'),
       (5, 1, [2], 2, 'claim'), (5, 1, [3], 1, 'claim'), (7, 1, [2], 1, 'claim'), (3, 2, [2], 1, 'claim')],
}
for c in cases[sys.argv[1]]: run(*c)
