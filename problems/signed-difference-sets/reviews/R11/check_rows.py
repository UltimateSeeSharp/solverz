"""Independent check of C8 (SupportParity, Lean nat semantics) and C1 on CSV rows and objects."""
import csv, re, sys, math, collections
from pathlib import Path
PF = Path(__file__).resolve().parents[3]
KEY = re.compile(r"SDS\((-?\d+),(-?\d+),(-?\d+),\[([\d,]*)\]\)")

def nsub(a, b):  # Lean Nat subtraction
    return a - b if a >= b else 0

def sp_lean(v, k, lam):  # literal transcription of Parity.lean SupportParity
    return v % 2 == 1 and lam % 2 == 0 and nsub(v, k) * nsub(nsub(v, k), 1) < nsub(v, 1)

def sp_int(v, k, lam):  # C8 in plain integers (d may be negative)
    d = v - k
    return v % 2 == 1 and lam % 2 == 0 and d * (d - 1) < v - 1

def is_sq(n):
    return n >= 0 and math.isqrt(n) ** 2 == n

rows = list(csv.DictReader(open(PF / "instances.csv", encoding="utf-8")))
bad = []
st = collections.Counter()
fire = collections.defaultdict(list)
disagree = []
factor_issue = []
for r in rows:
    m = KEY.fullmatch(r["key"])
    if not m:
        bad.append(r["key"]); continue
    v, k, lam = map(int, m.groups()[:3])
    ms = [int(x) for x in m.group(4).split(",") if x]
    if math.prod(ms) != v or any(x <= 1 for x in ms) or not ms:
        factor_issue.append((r["id"], r["key"]))
    if k > v or k < 0:
        factor_issue.append((r["id"], r["key"], "k>v"))
    a, b = sp_lean(v, k, lam), sp_int(v, k, lam)
    if a != b:
        disagree.append((r["id"], r["key"], a, b))
    if a:
        fire[r["status"]].append((r["id"], r["key"], r["source"]))
print("unparsed", bad[:5], len(bad))
print("factor/k issues", factor_issue[:10], len(factor_issue))
print("lean vs int disagree", disagree[:10], len(disagree))
for s, l in fire.items():
    print("fires on status", s, len(l), collections.Counter(x[2].split('@')[0] for x in l))
print("exists rows fired:", fire.get("exists", []))
open_ids = {x[0] for x in fire.get("open", [])}
# sc_certs
sc = set(line.split()[0] for line in open(PF / "scratch" / "sc_certs.txt", encoding="utf-8") if line.strip())
print("sc_certs rows", len(sc), "open C8 rows not in sc_certs:", len(open_ids - sc), "in sc:", len(open_ids & sc))
# C1 on exists rows
nonsq = [(r["id"], r["key"]) for r in rows if r["status"] == "exists" and not is_sq((lambda v,k,l: k + l*(v-1))(*map(int, KEY.fullmatch(r["key"]).groups()[:3])))]
print("exists rows failing C1:", nonsq)
# ParityRows.lean data vs CSV
pr = Path(PF / "lean/SignedDifferenceSets/ParityRows.lean").read_text(encoding="utf-8")
lr = re.findall(r"⟨(\d+), \[([\d, ]+)\], (\d+), (-?\d+)⟩", pr)
csvmap = {r["id"]: r for r in rows}
mism = []
for i, ms, k, lam in lr:
    r = csvmap.get("N" + i)
    key = f"SDS({math.prod(int(x) for x in ms.split(','))},{k},{lam},[{ms.replace(' ', '')}])"
    if r is None or r["key"] != key or r["status"] != "open":
        mism.append((i, key, r and r["key"], r and r["status"]))
print("ParityRows.lean rows", len(lr), "mismatch with CSV", mism[:5], len(mism),
      "set equal to open fires:", {"N" + x[0] for x in lr} == open_ids)
