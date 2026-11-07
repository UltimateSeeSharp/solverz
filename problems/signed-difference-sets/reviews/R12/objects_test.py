# Real sets O1-O32: for every admissible certificate on the object's own group, the actual coset
# sums a satisfy C5's congruence, MomentsOk and BoxOk at (s' = sum a, t0 = a_0 mod q), and the
# mirrors of Kills / BoxKills reject that certificate. Controls: non-self-conjugate p.
import sys, math, itertools, glob, os, re
D0 = r"problems/signed-difference-sets"
sys.path.insert(0, D0 + "/reviews/R12")
from leanmirror import moments_ok, box_ok, kills, box_kills, factor

def load(path):
    L = open(path, encoding="utf-8").read().split("\n")
    head = L[0].split(); ms = [int(x) for x in head[0][1:].split("xC")]
    v, k, lam = map(int, head[1].strip("()").split(","))
    D = {}
    for l in L[1:]:
        if l.strip():
            *xs, sg = l.split(); D[tuple(int(x) for x in xs)] = 1 if sg == "+" else -1
    return ms, v, k, lam, D

def is_sds(ms, k, lam, D):
    if len(D) != k: return False
    els = list(itertools.product(*[range(m) for m in ms]))
    for g in els:
        if not any(g): continue
        t = sum(sv * D.get(tuple((a + b) % m for a, b, m in zip(x, g, ms)), 0) for x, sv in D.items())
        if t != lam: return False
    return True

tested = ctrl_fail = ctrl = 0
for path in sorted(glob.glob(D0 + "/objects/O*.txt"), key=lambda p: int(re.findall(r"O(\d+)", p)[0])):
    name = os.path.basename(path)
    ms, v, k, lam, D = load(path)
    if v > 1000: print(name, "skipped (v > 1000)"); continue
    assert math.prod(ms) == v and is_sds(ms, k, lam, D), name
    n = k - lam
    if n == 0: continue
    for p, e in factor(n).items():
        for j in range(1, e // 2 + 1):
            q = p ** j
            for ds in itertools.product(*[[d for d in range(1, m + 1) if m % d == 0] for m in ms]):
                h = math.prod(ds)
                if h == 1 or h % p == 0: continue
                a = {}
                for x, sv in D.items():
                    y = tuple(xi % d for xi, d in zip(x, ds)); a[y] = a.get(y, 0) + sv
                vec = [a.get(y, 0) for y in itertools.product(*[range(d) for d in ds])]
                c = v // h; L = math.lcm(*ds)
                i = next((i for i in range(1, 2 * L + 2) if (p ** i + 1) % L == 0), None)
                congr = all((x - vec[0]) % q == 0 for x in vec)
                if i is None:
                    ctrl += 1; ctrl_fail += not congr; continue
                sp, Q = sum(vec), sum(x * x for x in vec)
                assert sp * sp == k + lam * (v - 1) and Q == k + lam * (c - 1), name
                assert congr, (name, p, j, ds)
                t0 = vec[0] % q
                assert moments_ok(h, q, sp, Q, t0) and box_ok(h, q, sp, Q, t0, c), (name, p, j, ds, vec)
                assert not kills(ms, k, lam, p, j, i, list(ds), abs(sp)), (name, p, j, ds)
                assert not box_kills(ms, k, lam, p, j, i, list(ds), abs(sp)), (name, p, j, ds)
                tested += 1
    print(name, ms, (v, k, lam), "ok")
print("admissible (object, p, j, ds) tested:", tested, "| non-self-conjugate controls:", ctrl,
      "of which not congruent mod q:", ctrl_fail)
