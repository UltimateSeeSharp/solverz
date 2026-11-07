# Independent check of O12 and of the masks in the Lean file.
import re, sys
from collections import Counter
base = "problems/signed-difference-sets/"
lines = open(base + "objects/O12.txt").read().split("\n")
hdr = lines[0]; print("header:", hdr)
D = {}
for ln in lines[1:]:
    if not ln.strip(): continue
    a, b, s = ln.split()
    a, b = int(a), int(b)
    assert 0 <= a < 19 and 0 <= b < 19 and s in "+-", ln
    assert (a, b) not in D, ln
    D[(a, b)] = 1 if s == "+" else -1
print("marked:", len(D), "plus", sum(1 for v in D.values() if v == 1), "minus", sum(1 for v in D.values() if v == -1))
cnt = Counter()
for g1 in range(19):
    for g2 in range(19):
        if (g1, g2) == (0, 0): continue
        s = 0
        for (x1, x2), d in D.items():
            y = ((x1 + g1) % 19, (x2 + g2) % 19)
            s += d * D.get(y, 0)
        cnt[s] += 1
print("signed counts over g != 0:", dict(cnt))
# Masks from the Lean file
src = open(base + "lean/SignedDifferenceSets/Answer/N35840.lean", encoding="utf-8").read()
P = int(re.search(r"def plus : ℕ := (0x[0-9a-f]+)", src).group(1), 16)
N = int(re.search(r"def minus : ℕ := (0x[0-9a-f]+)", src).group(1), 16)
print("P bits", bin(P).count("1"), "N bits", bin(N).count("1"), "P&N", P & N, "P.bitlen", P.bit_length(), "N.bitlen", N.bit_length())
# Lean Indexed (ZMod 19 x ZMod 19): index = b + 19 * a  (first factor most significant)
E = {}
for i in range(361):
    a, b = divmod(i, 19)
    if (P >> i) & 1: E[(a, b)] = 1
    elif (N >> i) & 1: E[(a, b)] = -1
print("masks == O12:", E == D)
# Lean-style check simulating addIdx of the product instance
def addIdx(a, b):
    return ((a % 19) + (b % 19)) % 19 + 19 * (((a // 19) + (b // 19)) % 19)
def sgn(i):
    return 1 if (P >> i) & 1 else (-1 if (N >> i) & 1 else 0)
ok = sum(1 for i in range(361) if sgn(i) != 0) == 316
ok &= all(sum(sgn(x) * sgn(addIdx(x, g)) for x in range(361)) == 141 for g in range(1, 361))
print("checkSet simulation:", ok)
