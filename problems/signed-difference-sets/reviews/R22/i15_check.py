"""Independent check of I15's objects O40-O60 (and O38) and their Lean answer files."""
import csv, re, math, itertools
from pathlib import Path
P = Path(__file__).resolve().parents[3]
KEYRE = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
keys = {r["id"]: (r["key"], r["status"], r["evidence"]) for r in csv.DictReader(open(P / "instances.csv", encoding="utf-8"))}
objidx = {}
for line in (P / "objects/_objects.md").read_text(encoding="utf-8").splitlines():
    c = [x.strip() for x in line.split("|")]
    if len(c) > 5 and re.fullmatch(r"O\d+", c[1]): objidx[c[1]] = c[4]

def inv_factors(ms):
    """invariant factors (sorted, divisibility chain) of prod C_m"""
    pp = {}
    for m in ms:
        n, d = m, 2
        while n > 1:
            if n % d == 0:
                e = 0
                while n % d == 0: n //= d; e += 1
                pp.setdefault(d, []).append(d ** e)
            d += 1
    L = max((len(v) for v in pp.values()), default=0)
    out = [1] * L
    for p, v in pp.items():
        v = sorted(v, reverse=True)
        for i, x in enumerate(v): out[L - 1 - i] *= x
    return [x for x in out if x > 1]

def check_set(ms, D):
    """D: dict coord-tuple -> +-1. returns (k, set of lambdas over nonzero shifts)"""
    lams = set()
    for g in itertools.product(*[range(m) for m in ms]):
        if not any(g): continue
        t = 0
        for x, s in D.items():
            y = tuple((a + b) % m for a, b, m in zip(x, g, ms))
            t += s * D.get(y, 0)
        lams.add(t)
    return len(D), lams

def read_obj(o):
    first, *rest = (P / "objects" / f"{o}.txt").read_text(encoding="utf-8").splitlines()
    m = re.fullmatch(r"(\S+) \((\d+),(\d+),(-?\d+)\)", first.strip())
    ms = [int(x) for x in re.findall(r"C(\d+)", m[1])]
    D = {}
    for line in rest:
        if not line.strip(): continue
        *cs, s = line.split()
        x = tuple(int(c) for c in cs)
        assert len(x) == len(ms) and all(0 <= a < b for a, b in zip(x, ms)), (o, line)
        assert x not in D, (o, "dup", x)
        D[x] = {"+": 1, "-": -1}[s]
    return ms, int(m[2]), int(m[3]), int(m[4]), D

def read_lean(nid):
    t = (P / f"lean/SignedDifferenceSets/Answer/{nid}.lean").read_text(encoding="utf-8")
    plus = int(re.search(r"def plus : ℕ := (0x[0-9a-f]+)", t)[1], 16)
    minus = int(re.search(r"def minus : ℕ := (0x[0-9a-f]+)", t)[1], 16)
    hs = re.search(r"theorem hasSDS :\s*HasSDS \(([^)]*)\) (\d+) \(?(-?\d+)\)?\s*:=", t)
    grp = [int(x) for x in re.findall(r"ZMod (\d+)", hs[1])]
    sdsty = re.search(r"def sds : (.*) → SignType", t)[1]
    ranges = [(int(a), int(b)) for a, b in re.findall(r"allFrom \(shiftOk \([^)]*\) \(?-?\d+\)? plus minus\) (\d+) (\d+) = true", t)]
    chain = re.findall(r"allFrom_append h (shifts\d+)", t)
    return dict(t=t, plus=plus, minus=minus, grp=grp, k=int(hs[2]), lam=int(hs[3]), sdsty=sdsty,
                ranges=ranges, chain=chain, fast="isSDS_of_checkSet" in t, split="isSDS_of_checkSplit" in t)

def decode(grp, plus, minus):
    size = math.prod(grp); D = {}
    assert plus >> size == 0 and minus >> size == 0, "mask beyond size"
    for i in range(size):
        s = 1 if plus >> i & 1 else (-1 if minus >> i & 1 else 0)
        if s:
            x, r = [], i
            for m in reversed(grp): x.append(r % m); r //= m
            D[tuple(reversed(x))] = s
    return D

objs = [f"O{i}" for i in range(40, 61)] + ["O38"]
for o in objs:
    nid = objidx[o]
    key, status, ev = keys[nid]
    km = KEYRE.fullmatch(key); v, k, lam = int(km[1]), int(km[2]), int(km[3]); kms = [int(x) for x in km[4].split(",")]
    ms, ov, ok_, ol, D = read_obj(o)
    kk, lams = check_set(ms, D)
    probs = []
    if ms != kms: probs.append(f"obj group {ms} != key {kms}")
    if (ov, ok_, ol) != (v, k, lam): probs.append("obj header params")
    if kk != k: probs.append(f"weight {kk}")
    if lams != {lam}: probs.append(f"lambdas {sorted(lams)[:5]}")
    L = read_lean(nid)
    if L["grp"] != kms: probs.append(f"lean group {L['grp']}")
    if [int(x) for x in re.findall(r"ZMod (\d+)", L["sdsty"])] != kms: probs.append("sds type")
    if (L["k"], L["lam"]) != (k, lam): probs.append("lean params")
    LD = decode(L["grp"], L["plus"], L["minus"])
    if L["plus"] & L["minus"]: probs.append("plus&minus overlap")
    if LD != D: probs.append("lean masks != object")
    if L["split"]:
        r = L["ranges"]; pos = 0
        for lo, m in r:
            if lo != pos: probs.append(f"gap/overlap at {lo}")
            pos = lo + m
        if pos != v: probs.append(f"ranges end {pos} != {v}")
        if L["chain"] != [f"shifts{i}" for i in range(2, len(r) + 1)]: probs.append("chain")
        if not re.search(rf"countOk \([^)]*\) {k} plus minus", L["t"]): probs.append("count k")
        nr = len(r)
    else:
        nr = 0
        if not L["fast"]: probs.append("neither fast nor split")
    print(o, nid, key, status, "k", kk, "lams", sorted(lams), "split" if L["split"] else "fast", nr, "OK" if not probs else probs)
