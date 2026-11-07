# Independent: parse the Lean chunks' text, compare each entry with instances.csv.
import csv, re, sys, math
from collections import Counter
PF = r"problems/signed-difference-sets"
ENTRY = re.compile(r"\(⟨(\d+), \[([0-9, ]*)\], (\d+), (-?\d+)⟩, ⟨(\d+), (\d+), (\d+), \[([0-9, ]*)\], (-?\d+)⟩\)")
rows = {r["id"]: r for r in csv.DictReader(open(PF + "/instances.csv", encoding="utf-8"))}
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
entries = []
for n in range(1, 14):
    txt = open(PF + f"/lean/SignedDifferenceSets/SelfConjugacyRows/Part{n:02d}.lean", encoding="utf-8").read()
    body = txt.split(":= [", 1)[1].split("]\n\nset_option", 1)[0]
    found = ENTRY.findall(body)
    # count raw lines starting with "  (⟨" to catch any entry the regex missed
    raw = [l for l in body.splitlines() if l.strip()]
    assert len(found) == len(raw), (n, len(found), len(raw))
    # theorem names/statement shape
    assert f"theorem part{n:02d}_kills : ∀ x ∈ part{n:02d}, x.2.Kills x.1 := by decide +kernel" in txt
    assert f"ScCert.not_hasSDS (part{n:02d}_kills x hx) inst" in txt
    for f in found:
        entries.append((n,) + f)
print("entries", len(entries))
ids = Counter(e[1] for e in entries)
print("dup ids", [i for i, c in ids.items() if c > 1])
bad = 0
for e in entries:
    n, nid, ms, k, lam = e[0], e[1], e[2], e[3], e[4]
    r = rows.get("N" + nid)
    if r is None: print("missing row", nid); bad += 1; continue
    m = KEY.fullmatch(r["key"])
    v, kk, ll = int(m.group(1)), m.group(2), m.group(3)
    mms = [int(x) for x in m.group(4).split(",")]
    lms = [int(x) for x in ms.split(", ")] if ms else []
    if lms != mms or kk != k or ll != lam:
        print("MISMATCH", nid, r["key"], ms, k, lam); bad += 1
    if math.prod(mms) != v: print("v != prod", nid, r["key"]); bad += 1
    if r["status"] != "open": print("status", nid, r["status"]); bad += 1
print("bad", bad)
openrows = [i for i, r in rows.items() if r["status"] == "open"]
print("open rows", len(openrows), "in chunks", sum(1 for i in openrows if i[1:] in ids))
# check all instances.csv keys: v = prod for all rows, and key regex fullmatch
nonmatch = [r["id"] for r in rows.values() if not KEY.fullmatch(r["key"])]
print("keys not matching regex", nonmatch[:5], len(nonmatch))
# order of ids
prev = 0
for e in entries:
    assert int(e[1]) > prev; prev = int(e[1])
print("ids increasing")
