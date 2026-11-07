# Which of the 144 kills are the plain 3-adic congruence (gcd(T(n), N) does not divide s) and which need the count?
import re, math, collections
from pathlib import Path
from kill20 import traces, kills
PF = Path(__file__).resolve().parents[3]
src = (PF / "lean/SignedDifferenceSets/EisensteinCharsRows.lean").read_text(encoding="utf-8")
ent = re.findall(r"\(⟨(\d+), \[([\d, ]+)\], (\d+), (-?\d+)⟩, ⟨\[([\d, ]+)\], (-?\d+)⟩\)", src)
cnt = collections.Counter(); ex = collections.defaultdict(list)
for i, ms, k, lam, ds, s in ent:
    k, lam, s = int(k), int(lam), int(s); N = math.prod(int(d) for d in ds.split(",")); n = k - lam
    T = traces(n); g = math.gcd(N, *T) if T else N
    e3 = 0; m = n
    while m % 3 == 0: m //= 3; e3 += 1
    kind = "gcd" if s % g else "count"
    cnt[(kind, N, e3)] += 1; ex[(kind, N, e3)].append((i, n, s, sorted(T)[:6]))
for key in sorted(cnt): print(key, cnt[key], ex[key][:3])
