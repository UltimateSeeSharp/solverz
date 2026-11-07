"""O37 in Z6 x Z37 coordinates: D(a, b) by b's order-4 cyclotomic class (generator 2)."""
import sys
sys.path.insert(0, ".")
from check import load
v, k, lam, D = load("O37")
cls = {0: "0"}
x = 1
for i in range(36):
    cls[x] = i % 4
    x = x * 2 % 37
tab = {}
for z in range(v):
    a, b = z % 6, z % 37
    tab.setdefault((a, cls[b]), set()).add(D[z])
for a in range(6):
    print(a, [sorted(tab[(a, c)]) for c in ["0", 0, 1, 2, 3]])
