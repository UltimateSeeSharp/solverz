# Compare turyn.py's rule() with indep.py per Instance (all statuses).
import csv, re, sys
src = open(sys.argv[1], encoding="utf-8").read()
ns = {}; exec(src.split("rows = list(")[0], ns)
mine = {l.split()[0] for l in open(sys.argv[3], encoding="utf-8")}
theirs = set()
for r in csv.DictReader(open(sys.argv[2], encoding="utf-8")):
    m = ns["KEY"].fullmatch(r["key"]); v, k, lam = map(int, m.groups()[:3])
    shape = [int(x) for x in m.group(4).split(",")]
    if ns["rule"](v, k, lam, shape): theirs.add(r["id"])
print("turyn.py:", len(theirs), "indep:", len(mine), "only turyn:", sorted(theirs - mine)[:10], "only indep:", sorted(mine - theirs)[:10])
