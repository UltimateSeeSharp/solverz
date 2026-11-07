# Brute-force test of the lemma behind rule SC, independent of SDS: on small H, enumerate all
# a in [-B,B]^H whose autocorrelation is constant off the identity (a a^-1 = n + mu H), and
# check a_h = const mod p^j for every prime p, p^(2j) | n, p not dividing |H|, p self-conjugate
# mod exp(H). Control: count violations for non-self-conjugate p too (must exist somewhere).
import sys, itertools, math, numpy as np
sys.path.insert(0, ".")
from indep import factor, selfconj

def group(shape):
    els = list(itertools.product(*[range(m) for m in shape]))
    idx = {g: i for i, g in enumerate(els)}
    add = np.array([[idx[tuple((x + y) % m for x, y, m in zip(g, h, shape))] for h in els] for g in els])
    return els, add

def run(shape, B, chunk=1 << 20):
    els, add = group(shape); N = len(els); m = math.lcm(*shape)
    vals = np.arange(-B, B + 1, dtype=np.int64); total = (2 * B + 1) ** N
    stats = dict(sols=0, tested=0, viol_sc=0, viol_ctrl=0, ctrl_tested=0)
    examples = []
    for start in range(0, total, chunk):
        ids = np.arange(start, min(total, start + chunk), dtype=np.int64)
        A = np.empty((len(ids), N), dtype=np.int64); t = ids.copy()
        for i in range(N): A[:, i] = vals[t % (2 * B + 1)]; t //= (2 * B + 1)
        ac = np.stack([(A * A[:, add[:, g]]).sum(1) for g in range(1, N)], 1)  # shifts g != 0
        ok = (ac == ac[:, :1]).all(1)
        for a, mu in zip(A[ok], ac[ok][:, 0]):
            n = int((a * a).sum()) - int(mu)
            if n <= 0: continue
            stats["sols"] += 1
            for p, e in factor(n).items():
                j = e // 2
                if j == 0 or N % p == 0: continue
                q = p ** j; const = bool(((a - a[0]) % q == 0).all())
                if selfconj(p, m):
                    stats["tested"] += 1; stats["j2"] = stats.get("j2", 0) + (j >= 2)
                    if not const: stats["viol_sc"] += 1; examples.append((shape, a.tolist(), n, int(mu), p, j))
                else:
                    stats["ctrl_tested"] += 1; stats["viol_ctrl"] += (not const)
    return stats, examples[:3]

for shape, B in [((3,), 14), ((4,), 9), ((5,), 6), ((2, 2), 10), ((7,), 3)]:
    s, ex = run(list(shape), B)
    print(shape, "B", B, s, ex, flush=True)
