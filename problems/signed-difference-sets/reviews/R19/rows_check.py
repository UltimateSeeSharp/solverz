# Parse EisensteinCharsRows.lean, match to instances.csv, recompute kills.
import re, csv, math, sys
from pathlib import Path
from kill20 import kills, traces
PF = Path(__file__).resolve().parents[3]
src = (PF / "lean/SignedDifferenceSets/EisensteinCharsRows.lean").read_text(encoding="utf-8")
ent = re.findall(r"\(⟨(\d+), \[([\d, ]+)\], (\d+), (-?\d+)⟩, ⟨\[([\d, ]+)\], (-?\d+)⟩\)", src)
print("entries", len(ent), "chunks", re.findall(r"def (eisensteinCharsRows\d+)", src))
inst = {r["id"]: r for r in csv.DictReader(open(PF / "instances.csv", encoding="utf-8"))}
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
ids = [e[0] for e in ent]; assert len(set(ids)) == len(ids), "dup ids"
bad = 0; Ns = {}
for i, ms, k, lam, ds, s in ent:
    ms = [int(x) for x in ms.split(",")]; ds = [int(x) for x in ds.split(",")]; k = int(k); lam = int(lam); s = int(s)
    r = inst.get("N" + i)
    m = KEY.fullmatch(r["key"]); v0, k0, l0 = map(int, m.groups()[:3]); ms0 = [int(x) for x in m.group(4).split(",")]
    v = math.prod(ms)
    ok = (ms == ms0 and k == k0 and lam == l0 and v == v0 and r["status"] == "open"
          and len(ds) == len(ms) and all(d in (1, 3) and mm % d == 0 for d, mm in zip(ds, ms))
          and s * s == k + lam * (v - 1) and kills(math.prod(ds), s, k - lam))
    N = math.prod(ds); Ns[N] = Ns.get(N, 0) + 1
    if not ok: bad += 1; print("BAD", i, ms, k, lam, ds, s, r["key"], r["status"])
print("bad", bad, "by N", Ns)
