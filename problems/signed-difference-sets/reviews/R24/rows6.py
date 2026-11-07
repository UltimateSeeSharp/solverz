"""Independent recompute of C22 (Lean divisibility form) on instances.csv. Not derived from sylowrows.py."""
import csv, re, sys, math
from collections import Counter
PAIRS = {2: [1, 2, 4, 8, 16, 32, 64, 128], 3: [1, 3, 9, 27, 81], 5: [1, 5, 25], 7: [1, 7, 49],
         11: [1, 11], 13: [1, 13], 17: [1], 19: [1]}

def vp(x, p):
    if x == 0: return 10**6
    c = 0
    while x % p == 0: x //= p; c += 1
    return c

def parse(key):
    m = re.fullmatch(r'SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)', key)
    v, k, lam = int(m[1]), int(m[2]), int(m[3]); ms = [int(x) for x in m[4].split(',')]
    assert math.prod(ms) == v, key
    return v, k, lam, ms

def isqrt_exact(x):
    if x < 0: return None
    r = math.isqrt(x); return r if r * r == x else None

def lean_rule(v, k, lam, ms):
    """Best certificate of the Lean form: list of (p, r, e, q, t, s, ds) that kill."""
    s = isqrt_exact(k + lam * (v - 1))
    if s is None: return []
    n = k - lam
    out = []
    for p, rs in PAIRS.items():
        if v % p: continue
        e = min(vp(n, p), 200)
        for r in rs:
            J = vp(r * p, p)
            ds = [p ** min(vp(m, p), J) for m in ms]
            t = sum(min(vp(m, p), J) for m in ms)
            phi = (p - 1) * r
            q = -1
            while 2 * ((q + 1) * phi + 1) <= e * phi: q += 1
            if q < 0: continue
            if s % p ** min(t, q + 1): out.append((p, r, e, q, t, s, ds))
    return out

def c22_rule(v, k, lam, ms):
    """C22 as stated in claims/C22.md, full Sylow quotient, any prime."""
    s = isqrt_exact(k + lam * (v - 1))
    if s is None: return False
    n = k - lam
    if n <= 0: return False
    for p in range(2, v + 1):
        if v % p or any(p % d == 0 for d in range(2, int(p**0.5) + 1)): continue
        t = sum(vp(m, p) for m in ms); e = vp(n, p)
        if p > 2:
            if s % p ** min(t, (e + 1) // 2): return True
        else:
            m = isqrt_exact(n)
            if m is None: return True
            w = vp(m, 2)
            if s % 2 ** min(t, w): return True
            if w < t and s % 2 ** (w + 1) == 0: return True
    return False

if __name__ == '__main__':
    path = sys.argv[1]
    rows = list(csv.DictReader(open(path, encoding='utf-8')))
    hits = Counter(); c22h = Counter(); openhits = []
    for r in rows:
        v, k, lam, ms = parse(r['key'])
        h = lean_rule(v, k, lam, ms)
        if h:
            hits[r['status']] += 1
            if r['status'] == 'open': openhits.append((r['id'], h[0]))
            if r['status'] == 'exists': print('EXISTS HIT', r['id'], r['key'], h)
        if c22_rule(v, k, lam, ms):
            c22h[r['status']] += 1
            if r['status'] == 'exists': print('C22 EXISTS HIT', r['id'], r['key'])
    print(path, 'lean-form hits', dict(hits), 'C22-form hits', dict(c22h))
    with open(sys.argv[2], 'w') as f:
        for i, h in openhits: f.write(f'{i}\t{h}\n')
