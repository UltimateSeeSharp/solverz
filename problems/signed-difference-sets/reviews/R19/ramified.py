# Compare C20 (a <= 3-rank, any) with the ramified-prime congruence: 3^e || n, psi(D) in (1-w)^e, so
# N a0 - s' in (1-w)^e cap Z = 3^ceil(e/2) Z, hence 3^min(a, ceil(e/2)) | s; plus T(n) empty (n not a norm).
import re, csv, math
from pathlib import Path
from kill20 import kills, traces
PF = Path(__file__).resolve().parents[3]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
both = only20 = onlyR = 0; ex20 = []; exR = []
for r in csv.DictReader(open(PF / "instances.csv", encoding="utf-8")):
    m = KEY.fullmatch(r["key"]); v, k, lam = map(int, m.groups()[:3]); ms = [int(x) for x in m.group(4).split(",")]
    S = k + lam * (v - 1)
    if S < 0 or math.isqrt(S) ** 2 != S: continue
    s = math.isqrt(S); n = k - lam; c3 = sum(1 for x in ms if x % 3 == 0)
    if c3 == 0 or n <= 0: continue
    A = min(c3, 6)
    k20 = any(kills(3 ** a, s, n) for a in range(1, A + 1))
    e = 0; t = n
    while t % 3 == 0: t //= 3; e += 1
    kR = (not traces(n)) or s % 3 ** min(A, (e + 1) // 2) != 0
    if k20 and kR: both += 1
    elif k20: only20 += 1; ex20.append((r["id"], r["key"], r["status"], s, n))
    elif kR: onlyR += 1; exR.append((r["id"], r["key"], r["status"], s, n))
print("both", both, "C20 only", only20, ex20[:8], "ramified only", onlyR, exR[:8])
