"""Does C27's rule (any m | exp G, gcd(m,n)=1, any F | m with 1+FZ inside the multiplier group) fire on a row?
Usage: scan_exists.py ROOT STATUS"""
import csv, re, sys
from math import gcd, prod, lcm
from functools import reduce
from collections import Counter

def factor(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def totient(m):
    r = m
    for p in factor(m): r = r // p * (p - 1)
    return r
def gen_sub(p, m):
    s, x = set(), 1 % m
    while x not in s:
        s.add(x); x = x * p % m
    return s
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
def fires(v, k, lam, ms):
    n = k - lam
    if n <= 0: return None
    w = reduce(lcm, ms)
    for m in range(2, w + 1):
        if w % m or gcd(m, n) != 1: continue
        M = None
        for p in factor(n):
            S = gen_sub(p, m); M = S if M is None else M & S
        if M is None: M = set(range(m))  # n = 1: every unit
        for F in range(1, m + 1):
            if m % F: continue
            if all((1 + F * u) % m in M and gcd(1 + F * u, m) == 1 for u in range(m // F)):
                if m * F * (v // m) ** 2 < totient(m) * n:
                    return (m, F)
    return None
if __name__ == '__main__':
    root, status = sys.argv[1], sys.argv[2]
    cnt = Counter(); hits = []
    for r in csv.DictReader(open(root + "/instances.csv", encoding="utf-8")):
        if r["status"] != status: continue
        v, k, lam, ms = KEY.fullmatch(r["key"]).groups()
        v, k, lam, ms = int(v), int(k), int(lam), [int(x) for x in ms.split(",")]
        h = fires(v, k, lam, ms)
        cnt[bool(h)] += 1
        if h: hits.append((r["id"], r["key"], h))
    print(status, dict(cnt))
    for x in hits[:30]: print(x)
    if status == "open":
        open("hits_open.txt", "w").write("\n".join(f"{a}\t{b}\t{c}" for a, b, c in hits))
    