# Independent C19 kill test (not gausschars.py): exact integer sums via bitsets, then divisibility.
import math, csv, re
from pathlib import Path
PF = Path(__file__).resolve().parents[3]

def X(n):
    m = math.isqrt(n)
    return sorted({x for x in range(-m, m + 1) if math.isqrt(n - x * x) ** 2 == n - x * x})

import functools
@functools.lru_cache(maxsize=None)
def pair_sums(n, P):
    """set of exact integers sum of P values 2x, x in X(n); as offset bitset (python int)."""
    m = math.isqrt(n); xs = X(n); off = 2 * P * m
    bs = 1 << off  # value 0 at bit off
    for _ in range(P):
        nb = 0
        for x in xs:
            sh = 2 * x
            nb |= (bs << sh) if sh >= 0 else (bs >> -sh)
        bs = nb
    return frozenset(i - off for i in range(bs.bit_length()) if bs >> i & 1)

def reachable(N, m, sp, R, n):
    """is N | sp + m*t + S for t in {-(R-1),..,R-1 step 2}, S a pair sum with P = (N-R)/2."""
    P = (N - R) // 2
    S = pair_sums(n, P)
    Smod = {x % N for x in S}
    for t in range(-(R - 1), R, 2):
        if (-(sp + m * t)) % N in Smod:
            return True
    return False

def kills(N, m, s, Rs=None):
    n = m * m
    if Rs is None:
        Rs = [R for R in range(1, N + 1) if (N - R) % 2 == 0]
    return not any(reachable(N, m, sp, R, n) for sp in (s, -s) for R in Rs)

def parse(key):
    head, grp = key[4:-2].split(",[")
    v, k, lam = map(int, head.split(","))
    fs = [int(x) for x in grp.split(",")]
    assert math.prod(fs) == v
    return v, k, lam, fs

def rows():
    for r in csv.DictReader(open(PF / "instances.csv", encoding="utf-8")):
        yield r
