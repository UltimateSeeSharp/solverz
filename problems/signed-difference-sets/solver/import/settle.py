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

instance, status, evidence, lean, *solution = sys.argv[1:6]
assert status in STATUSES, f"status must be one of {STATUSES}"
with OUT.open(encoding="utf-8", newline="") as f:
    reader = csv.DictReader(f)
    header, rows = reader.fieldnames, list(reader)
matches = [r for r in rows if r["id"] == instance]
assert len(matches) == 1, f"no Instance {instance}"
row = matches[0]
assert row["status"] in ("open", status), f"{instance} is {row['status']} ({row['evidence']})"
row.update(status=status, evidence=evidence, lean=lean)
if solution:
    row["solution"] = solution[0]
with OUT.open("w", encoding="utf-8", newline="") as f:
    writer = csv.DictWriter(f, header, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
print(f"{instance} {row['key']}: {status}")
