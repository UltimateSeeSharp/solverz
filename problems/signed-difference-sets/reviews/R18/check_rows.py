# Check the 297 certificates of GaussCharsRows.lean against instances.csv and recompute the kill.
import re, math, sys
from pathlib import Path
from kill import PF, kills, parse, rows
src = (PF / "lean/SignedDifferenceSets/GaussCharsRows.lean").read_text(encoding="utf-8")
ent = re.findall(r"\(⟨(\d+), \[([\d, ]+)\], (\d+), (-?\d+)⟩, ⟨\[([\d, ]+)\], (-?\d+), (-?\d+)⟩\)", src)
print("entries", len(ent))
tab = {r["id"]: r for r in rows()}
bad = []; ids = set(); trueR_fail = []
for i, ms, k, lam, ds, m, s in ent:
    ms = [int(x) for x in ms.split(", ")]; ds = [int(x) for x in ds.split(", ")]
    k, lam, m, s = int(k), int(lam), int(m), int(s)
    rid = "N" + i
    if rid in ids: bad.append((rid, "dup"))
    ids.add(rid)
    r = tab.get(rid)
    if r is None: bad.append((rid, "missing")); continue
    v, k2, lam2, fs = parse(r["key"])
    if (fs, k2, lam2) != (ms, k, lam): bad.append((rid, "key", r["key"]))
    if r["status"] != "open": bad.append((rid, "status", r["status"]))
    if len(ds) != len(ms) or any(mm % d for d, mm in zip(ds, ms)) or any(4 % d for d in ds): bad.append((rid, "ds"))
    if m < 0 or m * m != k - lam: bad.append((rid, "m"))
    if s * s != k + lam * (v - 1): bad.append((rid, "s"))
    N = math.prod(ds)
    if not kills(N, m, s): bad.append((rid, "nokill", N, m, s))
    # true R for this H: 2^(number of even d)
    R = 2 ** sum(1 for d in ds if d % 2 == 0)
    if not kills(N, m, s, [R]): trueR_fail.append(rid)
print("bad", bad)
print("trueR fails (should be empty)", trueR_fail)
