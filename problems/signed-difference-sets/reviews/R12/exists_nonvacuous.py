import csv, re, sys
D = r"problems/signed-difference-sets"
sys.path.insert(0, D + "/reviews/R12")
from leanmirror import all_certs
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
n_rows = n_certs = 0; ex = []
for r in csv.DictReader(open(D + "/instances.csv", encoding="utf-8")):
    if r["status"] != "exists": continue
    m = KEY.fullmatch(r["key"]); k, lam = int(m.group(2)), int(m.group(3)); ms = [int(x) for x in m.group(4).split(",")]
    c = list(all_certs(ms, k, lam))
    if c: n_rows += 1; n_certs += len(c); ex.append(r["id"] + " " + r["key"])
print("exists rows with >= 1 admissible certificate:", n_rows, "certificates:", n_certs, ex[:8])
