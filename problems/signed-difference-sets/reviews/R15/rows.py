# Independent recompute of C17 on instances.csv: closed form at r = R (full 2-rank) and a
# brute T-search at every r <= R; compare with scratch/real_chars.out.
import csv, math, sys, collections
from pathlib import Path
PF = Path(__file__).resolve().parents[3]

def v2(x, cap):
    if x == 0: return cap
    e = 0
    while x % 2 == 0 and e < cap: x //= 2; e += 1
    return e

def kills_closed(s, m, r):
    return min(v2(s, r), r) != min(v2(m, r), r)

def kills_search(s, m, r):
    N = 1 << r
    return not any((sp + m * T) % N == 0 for sp in (s, -s) for T in range(-(N - 1), N, 2))

def parse(key):
    head, grp = key[4:-2].split(",[")
    v, k, lam = map(int, head.split(","))
    fs = [int(x) for x in grp.split(",")]
    assert math.prod(fs) == v
    return v, k, lam, fs

def rule(v, k, lam, fs):
    """first r killing, or None; also asserts closed form == search for every r."""
    R = sum(1 for f in fs if f % 2 == 0)
    n, S = k - lam, k + lam * (v - 1)
    if R == 0 or n < 0 or S < 0: return None
    if math.isqrt(n) ** 2 != n or math.isqrt(S) ** 2 != S: return None
    s, m = math.isqrt(S), math.isqrt(n)
    first = None
    for r in range(1, R + 1):
        a, b = kills_closed(s, m, r), kills_search(s, m, r)
        assert a == b, (v, k, lam, fs, r)
        if a and first is None: first = r
    if first is not None: assert kills_closed(s, m, R)
    return first

if __name__ == "__main__":
    rows = list(csv.DictReader(open(PF / "instances.csv", encoding="utf-8")))
    hits = collections.defaultdict(list)
    for row in rows:
        v, k, lam, fs = parse(row["key"])
        r = rule(v, k, lam, fs)
        if r is not None: hits[row["status"]].append((row["id"], row["key"], r, row["evidence"]))
    for st, L in hits.items(): print(st, len(L), collections.Counter(x[2] for x in L))
    print("exists hits:", hits.get("exists", []))
    ref = {l.split()[0]: l.split() for l in open(PF / "scratch/real_chars.out")}
    mine = {x[0] for x in hits.get("open", [])}
    print("script 184 \ mine:", sorted(set(ref) - mine, key=lambda x: int(x[1:])))
    print("mine \ script:", sorted(mine - set(ref), key=lambda x: int(x[1:])))
    for x in hits.get("open", []):
        if x[0] not in ref: print("  extra", x[:3])
    for x in hits.get("open", []):
        if x[0] in ref and int(ref[x[0]][2]) != x[2]: print("  r differs", x[:3], ref[x[0]][2])
    noneev = collections.Counter(x[3].split(":")[0].split(";")[0][:25] for x in hits.get("none", []))
    print("none-row evidence of hits:", noneev.most_common(20))
    open(Path(__file__).parent / "rows.out", "w").write("".join(f"{a} {b} {c}\n" for a, b, c, _ in hits.get("open", [])))
