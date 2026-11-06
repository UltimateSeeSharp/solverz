"""Write our answer for one Instance into instances.csv; the importer keeps it on reruns.

Run from the problem folder:
python -I solver/import/settle.py <id> <exists|none> <evidence: our IDs> <lean theorem> [<Solution ID>]
python -I solver/import/settle.py --batch <file>: one row per line, tab-separated
`id status evidence lean [solution]`; all rows checked before anything is written.
"""

import csv
import sys
from pathlib import Path

OUT = Path(__file__).resolve().parents[2] / "instances.csv"
STATUSES = {"exists", "none"}
OPEN = "open"
BATCH = "--batch"

if sys.argv[1] == BATCH:
    with open(sys.argv[2], encoding="utf-8") as f:
        updates = [line.rstrip("\n").split("\t") for line in f if line.strip()]
else:
    updates = [sys.argv[1:6]]
with OUT.open(encoding="utf-8", newline="") as f:
    reader = csv.DictReader(f)
    header, rows = reader.fieldnames, list(reader)
by_id = {r["id"]: r for r in rows}
assert len({u[0] for u in updates}) == len(updates), "an Instance appears twice"
for instance, status, evidence, lean, *solution in updates:
    assert status in STATUSES, f"status must be one of {STATUSES}"
    assert instance in by_id, f"no Instance {instance}"
    row = by_id[instance]
    assert row["status"] in (OPEN, status), f"{instance} is {row['status']} ({row['evidence']})"
for instance, status, evidence, lean, *solution in updates:
    by_id[instance].update(status=status, evidence=evidence, lean=lean)
    if solution:
        by_id[instance]["solution"] = solution[0]
with OUT.open("w", encoding="utf-8", newline="") as f:
    writer = csv.DictWriter(f, header, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
for instance, status, *_ in updates[:3]:
    print(f"{instance} {by_id[instance]['key']}: {status}")
print(f"{len(updates)} rows settled")
