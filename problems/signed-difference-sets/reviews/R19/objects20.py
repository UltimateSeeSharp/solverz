import re, math
from pathlib import Path
from eis_lib import is_sds, eis_check
PF = Path(__file__).resolve().parents[3]
def load(i):
    L = (PF / f"objects/O{i}.txt").read_text(encoding="utf-8").split("\n")
    m = re.match(r"(\S+) \((\d+),(\d+),(-?\d+)\)", L[0])
    ms = [int(x) for x in m.group(1).replace("C", "").split("x")]
    D = {}
    for l in L[1:]:
        p = l.split()
        if p: D[tuple(int(x) for x in p[:-1])] = 1 if p[-1] == "+" else -1
    return ms, int(m.group(2)), int(m.group(3)), int(m.group(4)), D
for i in range(1, 40):
    ms, v, k, lam, D = load(i)
    if not any(m % 3 == 0 for m in ms): continue
    assert math.prod(ms) == v and len(D) == k
    ok = is_sds(ms, D, lam)
    viol, fired, r = eis_check(ms, D, k, lam)
    print(f"O{i} {ms} ({v},{k},{lam}) sds={ok} 3-rank={r} viol={len(viol)} {viol[:3]} fired={fired}")
