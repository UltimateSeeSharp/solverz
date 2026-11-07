# (a) the mirror accepts every chunk entry (decide must succeed); (b) every admissible certificate
# on every `exists` row: none kills; (c) admissible certificates on all open rows: kill set.
import csv, re, sys, math
sys.path.insert(0, r"problems/signed-difference-sets/reviews/R12")
from leanmirror import kills, all_certs
PF = r"problems/signed-difference-sets"
ENTRY = re.compile(r"\(⟨(\d+), \[([0-9, ]*)\], (\d+), (-?\d+)⟩, ⟨(\d+), (\d+), (\d+), \[([0-9, ]*)\], (-?\d+)⟩\)")
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
L = {}
for n in range(1, 14):
    txt = open(PF + f"/lean/SignedDifferenceSets/SelfConjugacyRows/Part{n:02d}.lean", encoding="utf-8").read()
    for f in ENTRY.findall(txt):
        ms = [int(x) for x in f[1].split(", ")]; ds = [int(x) for x in f[7].split(", ")]
        r = kills(ms, int(f[2]), int(f[3]), int(f[4]), int(f[5]), int(f[6]), ds, int(f[8]))
        L["N" + f[0]] = r
print("chunk entries", len(L), "mirror rejects", [i for i, r in L.items() if not r][:10],
      "C5", sum(r == "C5" for r in L.values()), "C6", sum(r == "C6" for r in L.values()))
rows = list(csv.DictReader(open(PF + "/instances.csv", encoding="utf-8")))
mine = {}
for r in rows:
    if r["status"] not in sys.argv[1].split(","): continue
    m = KEY.fullmatch(r["key"]); k, lam = int(m.group(2)), int(m.group(3))
    ms = [int(x) for x in m.group(4).split(",")]
    for cert in all_certs(ms, k, lam):
        why = kills(ms, k, lam, *cert)
        if why:
            mine[r["id"]] = (r["status"], r["key"], why, cert); break
from collections import Counter
print("admissible-cert kills by status", Counter(v[0] for v in mine.values()))
for i, v in mine.items():
    if v[0] != "open": print("KILLED", i, v)
op = {i for i, v in mine.items() if v[0] == "open"}
print("open: mine", len(op), "chunks", len(L), "mine-chunks", sorted(op - set(L), key=lambda x: int(x[1:]))[:20],
      "chunks-mine", sorted(set(L) - op, key=lambda x: int(x[1:]))[:20])
