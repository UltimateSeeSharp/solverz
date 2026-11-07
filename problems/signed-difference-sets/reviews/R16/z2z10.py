"""Consistency: C5 (Lean) says no SDS(20,11,2) in Z2 x Z10, so by C18's identity no (10,2,9,4) RDS there.
Exhaust: every H of order 2, every R missing H and meeting each other coset once (translation WLOG). Control: Z20."""
import itertools

def run(G, add, neg, zero):
    found = 0
    elems = list(G)
    for h in elems:
        if h == zero or add(h, h) != zero:
            continue
        H = [zero, h]
        cosets, seen = [], set()
        for g in elems:
            if g in seen: continue
            c = [g, add(g, h)]; seen.update(c); cosets.append(c)
        others = [c for c in cosets if zero not in c]
        for pick in itertools.product((0, 1), repeat=len(others)):
            R = [c[i] for c, i in zip(others, pick)]
            cnt = {}
            for a in R:
                for b in R:
                    if a != b:
                        d = add(a, neg(b)); cnt[d] = cnt.get(d, 0) + 1
            if cnt.get(h, 0) == 0 and all(cnt.get(g, 0) == 4 for g in elems if g not in H):
                found += 1
                # and R - H is an SDS (20,11,2)?
                D = {g: 0 for g in elems}
                for a in R: D[a] = 1
                for x in H: D[x] = -1
                ok = all(sum(D[x] * D[add(x, g)] for x in elems) == 2 for g in elems if g != zero)
                assert ok
    return found

Z2Z10 = [(a, b) for a in range(2) for b in range(10)]
print("Z2xZ10 RDS(10,2,9,4) count:", run(Z2Z10, lambda x, y: ((x[0]+y[0]) % 2, (x[1]+y[1]) % 10),
      lambda x: ((-x[0]) % 2, (-x[1]) % 10), (0, 0)))
print("Z20 control count:", run(list(range(20)), lambda x, y: (x + y) % 20, lambda x: (-x) % 20, 0))
