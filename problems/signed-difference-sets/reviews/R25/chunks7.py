# Parse SylowTwoRows.lean; check keys against instances.csv, re-implement SyTwoCert.Kills, check the tsv chunks.
import re, csv, math, sys
from math import isqrt
P = "../../../"
src = open(P + "lean/SignedDifferenceSets/SylowTwoRows.lean", encoding="utf-8").read()
chunks = re.split(r"def sylowTwoRows(\d+) : List \(Row × SyTwoCert\) := \[", src)
ENTRY = re.compile(r"\(⟨(\d+), \[([\d, ]*)\], (\d+), (-?\d+)⟩,\s*⟨(\d+), (-?\d+), (\d+), (\d+), (-?\d+), \[([\d, ]*)\]⟩\)")
inst = {}
with open(P + "instances.csv", newline="", encoding="utf-8") as f:
    for r in csv.DictReader(f):
        inst[r["id"]] = r
maPairs2 = {1, 2, 4, 8, 16, 32, 64, 128}
L = lambda s: [int(x) for x in s.replace(" ", "").split(",") if x]
def ispow2(d): return d > 0 and d & (d - 1) == 0
def kills(ms, k, lam, c):
    r, m, w, t, s, ds = c
    ok = 0 < r and all(x > 0 for x in ms) and len(ds) == len(ms) and all(m_ % d == 0 for d, m_ in zip(ds, ms))
    ok = ok and all(d > 0 and (2 * r) % d == 0 and ispow2(d) for d in ds)
    ok = ok and k - lam == m * m and m % (2 ** w) == 0 and m % (2 ** (w + 1)) != 0
    ok = ok and w < t and math.prod(ds) == 2 ** t and s * s == k + lam * (math.prod(ms) - 1)
    ok = ok and s % (2 ** (w + 1)) == 0 and r in maPairs2
    return ok
where = {}; nbad = 0; n = 0
for j in range(1, len(chunks), 2):
    cid = int(chunks[j]); body = chunks[j + 1].split("]\n\nset_option")[0]
    for e in ENTRY.finditer(body):
        n += 1
        i = "N" + e[1]; ms = L(e[2]); k = int(e[3]); lam = int(e[4])
        c = (int(e[5]), int(e[6]), int(e[7]), int(e[8]), int(e[9]), L(e[10]))
        where[i] = cid
        r = inst[i]
        key = f"SDS({math.prod(ms)},{k},{lam},[{','.join(map(str, ms))}])"
        if key != r["key"]: print("KEY MISMATCH", i, key, r["key"]); nbad += 1
        if r["status"] != "open": print("NOT OPEN", i, r["status"]); nbad += 1
        if not kills(ms, k, lam, c): print("KILLS FALSE", i, c); nbad += 1
        # sanity: the certificate's quotient is the full Sylow 2-part
        sy = [2 ** ((x & -x).bit_length() - 1) for x in ms]
        if c[5] != sy: print("NOT FULL SYLOW", i, c[5], sy)
print("entries", n, "bad", nbad)
for line in open(P + "scratch/settle-round7.tsv", encoding="utf-8"):
    f = line.rstrip("\n").split("\t")
    if f[0] in where:
        exp = f"SylowTwoRows chunk {where[f[0]]}"; thm = f"SignedDifferenceSets.sylowTwoRows{where[f[0]]}_not_hasSDS"
        if exp not in f[2] or f[3] != thm or f[1] != "none": print("TSV MISMATCH", f)
objs = open(P + "objects/_objects.md", encoding="utf-8").read() if __import__("os").path.exists(P + "objects/_objects.md") else ""
for i in where:
    if re.search(r"\b" + i + r"\b", objs): print("IN OBJECTS", i)
    if inst[i]["status"] == "exists" or inst[i]["solution"] or inst[i]["lean"]: print("HAS STUFF", i, inst[i])
print("tsv/objects checks done")
