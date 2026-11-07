"""Checks HalfRows.lean's rows against instances.csv, objects and the halving arithmetic (no solver imports)."""
import re, csv, math, glob, collections
from pathlib import Path
ROOT = Path(__file__).resolve().parents[3]
from rows_indep import factor, selfconj2, killing

def inv(ms):
    """Invariant-factor type: dict prime -> sorted exponents."""
    t = collections.defaultdict(list)
    for m in ms:
        for p, e in factor(m).items(): t[p].append(e)
    return {p: sorted(e) for p, e in t.items()}

def key_of(ms, k, lam): return f"SDS({math.prod(ms)},{k},{lam},[{','.join(map(str, ms))}])"

txt = chr(10).join(open(f, encoding="utf-8").read() for f in sorted((ROOT / "lean/SignedDifferenceSets/HalfRows").glob("Part*.lean")))
L = r"\[([\d, ]*)\]"
pat = re.compile(r"theorem (n\d+)_not_hasSDS \(inst : Fintype \(Grp " + L + r"\)\) :\s*¬ @HasSDS \(Grp " + L +
                 r"\) _ inst (\d+) \(?(-?\d+)\)? :=.*?HalfCert.not_hasSDS \(w := ⟨(\d+), " + L + r", (\d+), \(?(-?\d+)\)?⟩\)\s*"
                 r"\(c := ⟨(\d+), (\d+), " + L + r", \[(.*?)\], \[(.*?)\], " + L + r", (\d+), \(?(-?\d+)\)?,", re.S)
inst = {r["id"]: r for r in csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8"))}
bykey = {r["key"]: r for r in inst.values()}
okeys = set()
for f in glob.glob(str(ROOT / "objects/O*.txt")):
    h = open(f).readline().split(); ms = [int(x[1:]) for x in h[0].split("x")]; v, k, lam = h[1].strip("()").split(",")
    okeys.add((tuple(sorted((p, tuple(e)) for p, e in inv(ms).items())), int(k), int(lam)))
exists_types = collections.defaultdict(set)
for r in inst.values():
    if r["status"] == "exists":
        m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", r["key"]); ms = [int(x) for x in m.group(4).split(",")]
        exists_types[(int(m.group(1)), int(m.group(2)), int(m.group(3)))].add(r["id"])
tsv = {l.split("\t")[0] for l in open(ROOT / "scratch/c26/half_rows.tsv", encoding="utf-8") if l.strip()}
a7 = {l.split("\t")[0].strip() for l in open(ROOT / "scratch/settle-a7.tsv", encoding="utf-8") if l.strip()}
desc = {l.strip() for l in open(ROOT / "scratch/c26/rows.txt") if l.strip()}
ms_all = re.findall(r"theorem (n\d+)_not_hasSDS", txt)
found = pat.findall(txt); print("theorems", len(ms_all), "parsed", len(found))
issues = []; notes = collections.Counter()
for (name, g1, g2, k, lam, wid, wms, wk, wl, r, i, ks, A, P, ms2, k2, l2) in found:
    nid = "N" + wid; ms = [int(x) for x in g1.split(",")]; k, lam, k2, l2, r, i = map(int, (k, lam, k2, l2, r, i))
    ks = [int(x) for x in ks.split(",")]; ms2 = [int(x) for x in ms2.split(",")]
    if name != "n" + wid or g1 != g2 or g1 != wms or int(wk) != k or int(wl) != lam: issues.append((name, "statement/w mismatch"))
    if nid not in inst or inst[nid]["key"] != key_of(ms, k, lam): issues.append((name, "key", inst.get(nid, {}).get("key")))
    if inst[nid]["status"] != "open": issues.append((name, "status", inst[nid]["status"]))
    if nid not in tsv: issues.append((name, "not in tsv"))
    if nid in a7: issues.append((name, "in settle-a7"))
    if nid in desc: notes["also in DescentRows"] += 1
    v = math.prod(ms); n = k - lam
    if not (n > 0 and n % 4 == 0 and 4 * k2 == k + lam and 2 * l2 == lam and math.prod(ms2) * 2 == v): issues.append((name, "arith"))
    # G = C_{2r} x K with K of type ks, odd, selfconj; G/P = C_r x K must be the type of ms2
    if inv(ms) != inv([2 * r] + ks): issues.append((name, "G not C2r x K", inv(ms), inv([2 * r] + ks)))
    if inv(ms2) != inv([r] + ks if r > 1 else ks): issues.append((name, "ms2 not G/P", inv(ms2)))
    if any(d % 2 == 0 for d in ks) or not selfconj2(math.lcm(*ks)) or r & (r - 1): issues.append((name, "K/r"))
    S2 = k2 + l2 * (v // 2 - 1)
    if S2 >= 0 and math.isqrt(S2) ** 2 == S2:
        s2 = math.isqrt(S2)
        if s2 > k2: notes["halved |s| > k (trivially impossible)"] += 1
        elif s2 == k2: notes["halved s = k (ordinary DS forced)"] += 1
        else: notes["halved nontrivial"] += 1
    else: notes["halved s^2 not a square"] += 1
    if killing(ms, k, lam): notes["row also killed by parity"] += 1
    t2 = tuple(sorted((p, tuple(e)) for p, e in inv(ms2).items()))
    if (t2, k2, l2) in okeys: issues.append((name, "halved row has an object!"))
    hk = key_of(ms2, k2, l2)
    for kk, rr in bykey.items():
        pass
    same = exists_types.get((v // 2, k2, l2), set())
    for e in same:
        m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", inst[e]["key"])
        if inv([int(x) for x in m.group(4).split(",")]) == inv(ms2): issues.append((name, "halved row exists", e))
        else: notes["halved params exist in another group"] += 1
print("issues", len(issues)); [print(" ", x) for x in issues[:20]]
print(dict(notes))
print("tsv - lean", tsv - {"N" + f[5] for f in found}, "lean - tsv", {"N" + f[5] for f in found} - tsv)
