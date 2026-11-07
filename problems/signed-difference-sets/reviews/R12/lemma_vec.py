# momentsOk_of_congr / boxOk_of_congr in isolation: exhaustive small boxes + random vectors.
import sys, itertools, random
sys.path.insert(0, r"problems/signed-difference-sets/reviews/R12")
from leanmirror import moments_ok, box_ok
n_ok = n_const = 0
for N in range(1, 6):
    for q in (1, 2, 3, 4, 5, 7, 8, 9):
        for t in range(q):
            R = 3 if N <= 4 else 2
            for y in itertools.product(range(-R, R + 1), repeat=N):
                a = [t + q * x for x in y]
                sp, Q = sum(a), sum(x * x for x in a)
                c = max(abs(x) for x in a)
                const = len(set(a)) == 1
                for cc in (c, c + 1, c + q):
                    mo, bo = moments_ok(N, q, sp, Q, t), box_ok(N, q, sp, Q, t, cc)
                    if const:
                        assert not mo; n_const += 1
                    else:
                        assert mo and bo, (N, q, t, a, cc); n_ok += 1
random.seed(1)
for _ in range(200000):
    N = random.randint(2, 40); q = random.choice([2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 25, 27]); t = random.randrange(q)
    a = [t + q * random.randint(-6, 6) for _ in range(N)]
    if len(set(a)) == 1: continue
    sp, Q = sum(a), sum(x * x for x in a); c = max(abs(x) for x in a) + random.randint(0, 3)
    for s2, t2 in ((sp, t),):
        assert moments_ok(N, q, sp, Q, t) and box_ok(N, q, sp, Q, t, c), (N, q, t, a, c)
    n_ok += 1
print("vectors passing:", n_ok, "constant vectors rejected:", n_const)
