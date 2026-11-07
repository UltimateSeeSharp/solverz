# Brute force of C21's lemma: every Y in [-r, r]^H with constant off-zero autocorrelation mu, n = Y Ybar(0) - mu,
# e = v_p(n) >= 2 (or n = 0): check (1 - g_P) Y = 0 mod p^b (n = 0: exactly). H = C_{p^j} x K, own code.
import itertools, math, sys, collections
def vp(x, p):
    c = 0
    while x % p == 0: x //= p; c += 1
    return c
def run(p, j, K, r, label):
    hs = [p ** j] + K; els = list(itertools.product(*[range(m) for m in hs])); N = len(els)
    idx = {e: i for i, e in enumerate(els)}
    sh = [[idx[tuple((a + b) % m for a, b, m in zip(x, g, hs))] for x in els] for g in els]
    order = sorted(range(1, N), key=lambda t: t)  # shifts tested in order; reject on first mismatch
    s1 = sh[order[0]]
    gP = idx[(p ** (j - 1),) + (0,) * len(K)]
    pairs = [(i, sh[gP][i]) for i in range(N)]
    cnt = collections.Counter(); bad = []
    for Y in itertools.product(range(-r, r + 1), repeat=N):
        mu = sum(Y[i] * Y[s1[i]] for i in range(N))
        ok = True
        for t in order[1:]:
            s = sh[t]
            if sum(Y[i] * Y[s[i]] for i in range(N)) != mu: ok = False; break
        if not ok: continue
        n = sum(y * y for y in Y) - mu
        if n < 0: cnt['n<0'] += 1; continue
        if n == 0:
            cnt['n=0'] += 1
            if any(Y[a] != Y[b] for a, b in pairs): bad.append(('n=0', Y))
            continue
        e = vp(n, p); b = e // 2
        if b == 0: cnt['e<2'] += 1; continue
        cnt[('b', b)] += 1
        if any((Y[a] - Y[b2]) % p ** b for a, b2 in pairs): bad.append((n, Y))
    print(label, "H =", hs, "r =", r, dict(cnt), "violations:", len(bad), bad[:3], flush=True)
cases = {
    'a': [(2, 1, [3], 4, 'claim'), (2, 2, [3], 1, 'claim'), (2, 1, [5], 1, 'claim'), (5, 1, [2], 1, 'claim'),
          (3, 1, [4], 1, 'claim'), (3, 1, [2, 2], 1, 'claim'), (2, 3, [], 3, 'claim K=1'), (3, 1, [2], 4, 'claim'),
          (2, 1, [7], 1, 'CONTROL 2 not sc mod 7')],
    'b': [(7, 1, [2], 1, 'claim'), (2, 1, [3, 3], 1, 'claim'), (2, 1, [9], 1, 'claim'), (3, 2, [2], 1, 'claim'),
          (2, 4, [], 2, 'claim K=1'), (2, 2, [3], 2, 'claim')],
}
for c in cases[sys.argv[1]]: run(*c)
