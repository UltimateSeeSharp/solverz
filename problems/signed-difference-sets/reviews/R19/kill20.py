# Independent C20 kill: traces from an explicit (A, B) scan, reachability as a residue bitmask.
import math
from functools import lru_cache
@lru_cache(None)
def traces(n):
    if n < 0: return frozenset()
    r = math.isqrt(4 * n) + 2
    return frozenset(2 * A - B for A in range(-r, r + 1) for B in range(-r, r + 1) if A * A - A * B + B * B == n)
@lru_cache(None)
def reach_set(N, n, steps):
    # residues reachable as a sum of `steps` traces mod N
    S = {0}
    T = {t % N for t in traces(n)}
    for _ in range(steps): S = {(x + t) % N for x in S for t in T}
    return frozenset(S)
def kills(N, s, n):
    R = reach_set(N, n, (N - 1) // 2)
    return all((-sp) % N not in R for sp in (s, -s))
