# Validate the exhaustive search against instances.csv: every row in a searched group must be
# found iff it is not `none`-by-table (exists found; none not found; open reported).
import csv, re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent)); from rows import parse
PF = Path(__file__).resolve().parents[3]
found = {}; grp = None
for f in ["exh_le16.out", "exh_18.out", "exh_20.out"]:
    for l in open(Path(__file__).parent / f):
        m = re.match(r"group \[([\d, ]+)\]", l)
        if m: grp = tuple(int(x) for x in m.group(1).split(", ")); found[grp] = set(); continue
        m = re.match(r"\s+k=(\d+) lam=(-?\d+)", l)
        if m: found[grp].add((int(m.group(1)), int(m.group(2))))
bad = []; seen = 0
for row in csv.DictReader(open(PF / "instances.csv", encoding="utf-8")):
    v, k, lam, fs = parse(row["key"])
    if tuple(fs) not in found: continue
    seen += 1; hit = (k, lam) in found[tuple(fs)]
    if (row["status"] == "exists") != hit: bad.append((row["id"], row["key"], row["status"], hit))
print("rows in searched groups:", seen, "disagreements:", bad)
