"""Check O38, O39, sds_300_55_6.txt with own checker; structure: minus set = subgroup H, plus set = RDS missing H."""
import sys, re
from bose import sds_direct, sds_dft, is_rds

def load(path):
    lines = open(path).read().split("\n")
    m = re.match(r"C(\d+) \((\d+),(\d+),(-?\d+)\)", lines[0])
    v, v2, k, lam = map(int, m.groups()); assert v == v2
    D = [0] * v; seen = set()
    for ln in lines[1:]:
        if not ln.strip(): continue
        x, sgn = ln.split(); x = int(x)
        assert 0 <= x < v and x not in seen; seen.add(x)
        D[x] = 1 if sgn == "+" else -1
    return v, k, lam, D

PF = "../../../"
for f in [PF + "objects/O38.txt", PF + "objects/O39.txt", "../e10-objects/sds_300_55_6.txt"]:
    v, k, lam, D = load(f)
    N = [x for x in range(v) if D[x] == -1]; P = [x for x in range(v) if D[x] == 1]
    n = len(N); m = v // n
    Hsub = sorted(set((a + b) % v for a in N for b in N)) == sorted(N)
    rds = is_rds(P, v, m) if Hsub and N == list(range(0, v, m)) else None
    print(f, (v, k, lam), "SDS direct:", sds_direct(D, v, k, lam), "DFT err %.1e" % sds_dft(D, v, k, lam),
          "+%d -%d" % (len(P), n), "minus set = subgroup of order", n, ":", Hsub,
          "plus set RDS lam:", rds, "misses H:", not any(x % m == 0 for x in P))
a = load(PF + "objects/O39.txt")[3]; b = load("../e10-objects/sds_300_55_6.txt")[3]
print("O39 == sds_300_55_6.txt:", a == b)
