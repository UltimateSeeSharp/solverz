# Check the note's example grid: build/example.tex == O6 == Answer/N49.lean, and is a (25,12,1) SDS.
import re, sys
root = sys.argv[1]
o6 = open(root + "/objects/O6.txt", encoding="utf-8").read().split("\n")
D = {}
for ln in o6[1:]:
    if ln.strip():
        a, b, s = ln.split(); D[(int(a), int(b))] = 1 if s == "+" else -1
lean = open(root + "/lean/SignedDifferenceSets/Answer/N49.lean", encoding="utf-8").read()
rows = re.findall(r"!\[([-0-9, ]+)\]", lean)
L = {}
for a, r in enumerate(rows):
    for b, x in enumerate(r.split(",")):
        x = int(x)
        if x: L[(a, b)] = x
print("lean rows", len(rows), "O6==lean", D == L)
ex = open(root + "/papers/P1/build/example.tex", encoding="utf-8").read().splitlines()
grid = [l for l in ex if "&" in l]
E = {}
for a, l in enumerate(grid):
    cells = l.replace("\\\\", "").split("&")
    for b, c in enumerate(cells):
        c = c.strip()
        if c: E[(a, b)] = 1 if c == "+" else -1
print("example==O6", E == D, "rows", len(grid))
k = len(D)
bad = []
for g in [(i, j) for i in range(5) for j in range(5) if (i, j) != (0, 0)]:
    s = sum(D.get((a, b), 0) * D.get(((a + g[0]) % 5, (b + g[1]) % 5), 0) for a in range(5) for b in range(5))
    if s != 1: bad.append((g, s))
print("k", k, "bad shifts", bad, "sum", sum(D.values()), "s^2 should be", 12 + 1 * 24)
