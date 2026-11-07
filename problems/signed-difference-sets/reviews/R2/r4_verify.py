"""Independent check of R4 objects O6-O11 and their Lean tables."""
import itertools, re, sys, csv
from pathlib import Path

ROOT = Path(sys.argv[1])
CASES = {  # id: (object, lean file, factors, v, k, lam)
    "N49": ("O6", [5, 5], 25, 12, 1),
    "N61": ("O7", [3, 3, 3], 27, 10, 1),
    "N62": ("O8", [3, 9], 27, 10, 1),
    "N67": ("O9", [3, 3, 3], 27, 14, 5),
    "N68": ("O10", [3, 9], 27, 14, 5),
    "N73": ("O11", [3, 3, 3], 27, 17, 8),
}

def parse_obj(path):
    lines = path.read_text(encoding="utf-8").split("\n")
    head = lines[0]
    D = {}
    for ln in lines[1:]:
        ln = ln.strip()
        if not ln: continue
        *c, s = ln.split()
        D[tuple(int(x) for x in c)] = 1 if s == "+" else -1 if s == "-" else None
    return head, D

def parse_lean(path, factors):
    t = path.read_text(encoding="utf-8")
    m = re.search(r"def sds : (.*?) → SignType := fun p =>\s*(.*?)\n\s*p\.", t, re.S)
    typ, body = m.group(1), m.group(2)
    nums = [int(x) for x in re.findall(r"-?\d+", body)]
    cells = list(itertools.product(*[range(f) for f in factors]))
    assert len(nums) == len(cells), (len(nums), len(cells))
    D = {c: n for c, n in zip(cells, nums) if n != 0}
    accessor = re.search(r"\n\s*(p\.[^\n]*)\n", t[m.start():]).group(1)
    return typ.strip(), D, accessor.strip()

def is_sds(D, factors, k, lam):
    G = list(itertools.product(*[range(f) for f in factors]))
    add = lambda a, b: tuple((x + y) % f for x, y, f in zip(a, b, factors))
    if len(D) != k: return False, "size %d" % len(D)
    bad = []
    for g in G:
        if all(x == 0 for x in g): continue
        s = sum(D[x] * D.get(add(x, g), 0) for x in D)
        if s != lam: bad.append((g, s))
    # group-ring identity at 0 and squared sum
    tot = sum(D.values())
    ok_sq = tot * tot == (k - lam) + lam * len(G)
    return (not bad) and ok_sq, (bad[:5], tot)

rows = {}
with open(ROOT / "instances.csv", newline="") as f:
    for r in csv.DictReader(f):
        rows[r["id"]] = r

for nid, (oid, factors, v, k, lam) in CASES.items():
    head, Dobj = parse_obj(ROOT / "objects" / (oid + ".txt"))
    typ, Dlean, acc = parse_lean(ROOT / "lean/SignedDifferenceSets/Answer" / (nid + ".lean"), factors)
    key = "SDS(%d,%d,%d,[%s])" % (v, k, lam, ",".join(map(str, factors)))
    r = rows[nid]
    ok, info = is_sds(Dobj, factors, k, lam)
    okl, infol = is_sds(Dlean, factors, k, lam)
    plus = sum(1 for x in Dobj.values() if x == 1)
    print(nid, oid, "key", r["key"], r["key"] == key, "| head:", head, "| lean type:", typ, "| acc:", acc)
    print("   obj==lean", Dobj == Dlean, "| obj SDS", ok, info, "| lean SDS", okl, infol, "| +%d -%d" % (plus, len(Dobj) - plus))
