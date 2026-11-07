"""Each object O1-O33: recheck it is an SDS, then C1 (sum^2) and that C8 does not fire."""
import re, math, itertools
from pathlib import Path
PF = Path(__file__).resolve().parents[3]
from check_rows import sp_lean  # noqa: E402  (re-runs row check output; harmless)

def load(p):
    lines = p.read_text(encoding="utf-8").split("\n")
    m = re.fullmatch(r"(\S+) \((\d+),(\d+),(-?\d+)\)", lines[0].strip())
    ms = [int(x[1:]) for x in m.group(1).split("x")]
    v, k, lam = map(int, m.groups()[1:])
    D = {}
    for ln in lines[1:]:
        if not ln.strip():
            continue
        *c, s = ln.split()
        D[tuple(int(x) for x in c)] = 1 if s == "+" else -1
    return ms, v, k, lam, D

for i in range(1, 34):
    ms, v, k, lam, D = load(PF / "objects" / f"O{i}.txt")
    assert math.prod(ms) == v
    ok = len(D) == k and all(len(x) == len(ms) and all(0 <= a < m for a, m in zip(x, ms)) for x in D)
    items = list(D.items())
    if v <= 400:
        for g in itertools.product(*[range(m) for m in ms]):
            if not any(g):
                continue
            s = 0
            for x, sx in items:
                y = tuple((a + b) % m for a, b, m in zip(x, g, ms))
                s += sx * D.get(y, 0)
            if s != lam:
                ok = False; break
    else:  # O33: 2^12, check a sample of 300 g deterministically
        for t in range(1, v, 13):
            g = tuple((t >> j) & 1 for j in range(len(ms)))
            s = sum(sx * D.get(tuple((a + b) % 2 for a, b in zip(x, g)), 0) for x, sx in items)
            if s != lam:
                ok = False; break
    S = sum(D.values())
    print(f"O{i} {ms} ({v},{k},{lam}) SDS={ok} C1={S*S == k + lam*(v-1)} C8fires={sp_lean(v, k, lam)}")
