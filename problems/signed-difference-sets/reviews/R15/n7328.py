# Independent check of the evidence's 184th row N7328 SDS(176,29,4,[2,2,2,22]) (not C17's rule):
# coset sums on C2^r are a = H^-1 (s', m eps) (Walsh-Hadamard); need integral, |a_h| <= c,
# sum|a| <= k, k - sum|a| even (C4).
import itertools
v, k, lam = 176, 29, 4; s, m = 27, 5
for r in (3, 4):
    N = 1 << r; c = v // N
    H = [[(-1) ** bin(i & j).count("1") for j in range(N)] for i in range(N)]
    alive = 0
    for sp in (s, -s):
        for eps in itertools.product((1, -1), repeat=N - 1):
            f = (sp,) + tuple(m * e for e in eps)
            a = []
            for i in range(N):
                x = sum(H[i][j] * f[j] for j in range(N))
                if x % N: break
                a.append(x // N)
            else:
                t = sum(map(abs, a))
                if max(map(abs, a)) <= c and t <= k and (k - t) % 2 == 0: alive += 1
    print("r", r, "surviving patterns", alive)
