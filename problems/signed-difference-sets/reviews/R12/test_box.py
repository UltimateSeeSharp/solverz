# BoxRows chunks: row data vs instances.csv, mirror acceptance, admissible-cert kill sets,
# comparison with sc2_all.out (full sc2 incl. R2dp) on open rows, exists rows untouched.
import csv, re, sys, math
from collections import Counter
D = r"problems/signed-difference-sets"
sys.path.insert(0, D + "/reviews/R12")
from leanmirror import kills, box_kills, all_certs
ENTRY = re.compile(r"\(⟨(\d+), \[([0-9, ]*)\], (\d+), (-?\d+)⟩, ⟨(\d+), (\d+), (\d+), \[([0-9, ]*)\], (-?\d+)⟩\)")
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
rows = {r["id"]: r for r in csv.DictReader(open(D + "/instances.csv", encoding="utf-8"))}
def parse(folder, nparts):
    out = {}
    for n in range(1, nparts + 1):
        txt = open(D + f"/lean/SignedDifferenceSets/{folder}/Part{n:02d}.lean", encoding="utf-8").read()
        body = txt.split(":= [", 1)[1].split("]\n\nset_option", 1)[0]
        f = ENTRY.findall(body); raw = [l for l in body.splitlines() if l.strip()]
        assert len(f) == len(raw)
        for e in f:
            assert "N" + e[0] not in out, e[0]
            out["N" + e[0]] = ([int(x) for x in e[1].split(", ")], int(e[2]), int(e[3]), int(e[4]), int(e[5]), int(e[6]), [int(x) for x in e[7].split(", ")], int(e[8]))
    return out
B = parse("BoxRows", 3); S = parse("SelfConjugacyRows", 13)
print("box entries", len(B), "overlap with SC chunks", len(set(B) & set(S)))
bad = 0
for i, e in B.items():
    r = rows[i]; m = KEY.fullmatch(r["key"])
    if [int(x) for x in m.group(4).split(",")] != e[0] or int(m.group(2)) != e[1] or int(m.group(3)) != e[2] \
       or r["status"] != "open" or math.prod(e[0]) != int(m.group(1)):
        print("MISMATCH", i, r["key"], r["status"], e); bad += 1
print("row mismatches", bad)
print("mirror rejects box entries", [i for i, e in B.items() if not box_kills(*e)][:10])
# certs file agrees with Lean text
for l in open(D + "/scratch/box_certs.txt", encoding="utf-8"):
    nid, key, rule, p, j, i_, ds, s = l.split()
    e = B[nid]; assert (int(p), int(j), int(i_), [int(x) for x in ds.split(",")], int(s)) == e[3:], nid
# admissible certificates, all statuses open/exists
c5c13, box = {}, {}
for i, r in rows.items():
    if r["status"] not in ("open", "exists"): continue
    m = KEY.fullmatch(r["key"]); k, lam = int(m.group(2)), int(m.group(3))
    ms = [int(x) for x in m.group(4).split(",")]
    for cert in all_certs(ms, k, lam):
        if kills(ms, k, lam, *cert): c5c13[i] = r["status"]
        if box_kills(ms, k, lam, *cert): box[i] = r["status"]
print("exists killed: c5/c13", [i for i, s in c5c13.items() if s == "exists"], "box", [i for i, s in box.items() if s == "exists"])
op5 = {i for i, s in c5c13.items() if s == "open"}; opb = {i for i, s in box.items() if s == "open"}
print("open c5/c13", len(op5), "open box (any cert)", len(opb), "box-only", len(opb - op5),
      "box-only == chunk B", (opb - op5) == set(B), "B - opb", sorted(set(B) - opb)[:5])
sc2 = {l.split()[0]: l.split() for l in open(D + "/reviews/R4/sc2_all.out", encoding="utf-8")}
assert all(sc2[i][2] == rows[i]["key"] for i in rows), "sc2_all keys differ"
sk = {i for i, r in rows.items() if r["status"] == "open" and sc2[i][3] != "open"}
L = set(S) | set(B)
print("sc2 open-row kills", len(sk), "Lean C5+C13+C14", len(L), "sc2-Lean", sorted(sk - L)[:10], len(sk - L),
      "Lean-sc2", sorted(L - sk)[:10], len(L - sk))
print("sc2 first verdict on box rows", Counter(sc2[i][3] for i in B))
