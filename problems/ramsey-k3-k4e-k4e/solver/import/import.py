"""Write instances.csv: the one Instance, R(K3, K4-e, K4-e) >= 22, i.e. a valid colouring of K21.

Source: Radziszowski, Small Ramsey Numbers, DS1 revision 18 (2026-04-24): 21 <= R <= 22.
Run from the problem folder: python -I solver/import/import.py
"""

import csv
from pathlib import Path

HEADER = ["id", "key", "source", "status", "evidence", "lean", "solution"]
ROWS = [["N1", "R(K3,K4-e,K4-e) >= 22: K21", "21<=R<=22 @DS1 rev18", "open", "", "", ""]]

out = Path(__file__).resolve().parents[2] / "instances.csv"
with out.open("w", newline="", encoding="utf-8") as f:
    writer = csv.writer(f, lineterminator="\n")
    writer.writerow(HEADER)
    writer.writerows(ROWS)
print(f"wrote {out}")
