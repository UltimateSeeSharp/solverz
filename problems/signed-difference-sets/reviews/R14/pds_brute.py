"""C11 brute force: every symmetric P (0 not in P) in small abelian groups; if P is a PDS
(constant count lam' on P, mu off P, g != 0) with lam' = mu + 2, is P - {0} an SDS (v, |P|+1, mu)?
Also: does lam' - mu = 2 ever fail, and do other (lam', mu) ever give an SDS (sanity)."""
import itertools
def group(ms):
    els = list(itertools.product(*[range(m) for m in ms]))
    idx = {e: i for i, e in enumerate(els)}
    add = [[idx[tuple((a + b) % m for a, b, m in zip(x, y, ms))] for y in els] for x in els]
    neg = [idx[tuple((-a) % m for a, m in zip(x, ms))] for x in els]
    return els, add, neg
def run(ms):
    els, add, neg = group(ms)
    v = len(els)
    zero = 0
    classes, seen = [], {0}
    for x in range(1, v):
        if x not in seen:
            c = {x, neg[x]}; seen |= c; classes.append(sorted(c))
    sub = [[None] * v for _ in range(v)]
    for x in range(v):
        for y in range(v):
            sub[add[x][neg[y]]][y] = x  # x - y = add[x][neg y]
    stats = {"pds": 0, "lm2": 0, "lm2_ok": 0, "lm2_bad": 0}
    for mask in range(1 << len(classes)):
        P = set()
        for i, c in enumerate(classes):
            if mask >> i & 1:
                P |= set(c)
        cnt = [0] * v
        for x in P:
            for y in P:
                cnt[add[x][neg[y]]] += 1
        on = {cnt[g] for g in range(1, v) if g in P}
        off = {cnt[g] for g in range(1, v) if g not in P}
        if len(on) > 1 or len(off) > 1:
            continue
        stats["pds"] += 1
        lams = list(on) or list(range(0, v + 1))
        mus = list(off) or list(range(0, v + 1))
        for lp in lams:
            for mu in mus:
                if lp != mu + 2:
                    continue
                stats["lm2"] += 1
                D = [1 if x in P else (-1 if x == 0 else 0) for x in range(v)]
                ok = sum(1 for d in D if d) == len(P) + 1 and all(
                    sum(D[x] * D[add[x][g]] for x in range(v)) == mu for g in range(1, v))
                stats["lm2_ok" if ok else "lm2_bad"] += 1
    return v, stats
for ms in [(2,), (3,), (4,), (5,), (6,), (7,), (8,), (9,), (10,), (11,), (12,), (13,), (16,),
           (2, 2), (2, 4), (2, 2, 2), (3, 3), (2, 6), (4, 4), (2, 8), (2, 2, 4), (2, 2, 2, 2),
           (5, 5), (3, 6)]:
    print(ms, run(ms))
