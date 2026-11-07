"""Independent check of C23's 132 rows: data vs instances.csv, certificate arithmetic (Lean's
CmCert.Kills, literal), and an own search over every row (all statuses) for C23 kills."""
import csv, re, math, itertools, sys
from pathlib import Path
P = Path(__file__).resolve().parents[3]
KEYRE = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

def rows():
    out = {}
    for r in csv.DictReader(open(P / "instances.csv", encoding="utf-8")):
        m = KEYRE.fullmatch(r["key"])
        assert m, r["key"]
        v, k, lam = int(m[1]), int(m[2]), int(m[3])
        ms = [int(x) for x in m[4].split(",")]
        out[int(r["id"][1:])] = dict(v=v, k=k, lam=lam, ms=ms, status=r["status"], ev=r["evidence"], lean=r["lean"])
    return out

def lean_rows():
    t = (P / "lean/SignedDifferenceSets/CompositeModulusRows.lean").read_text(encoding="utf-8")
    pat = re.compile(r"\(⟨(\d+), \[([\d, ]+)\], (\d+), \(?(-?\d+)\)?⟩,\s*⟨\[([\d, ]+)\], \[([^\]]*)\], (-?\d+)⟩\)")
    res = []
    for m in pat.finditer(t):
        ps = [tuple(map(int, x)) for x in re.findall(r"\((\d+), (\d+), (\d+)\)", m[6])]
        res.append(dict(id=int(m[1]), ms=[int(x) for x in m[2].split(",")], k=int(m[3]), lam=int(m[4]),
                        ds=[int(x) for x in m[5].split(",")], ps=ps, s=int(m[7])))
    return res, t.count("(⟨")

def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True

def moments_ok(N, q, s, Q, t0):
    if (s - N * t0) % q or (Q - 2 * t0 * s + N * t0 * t0) % (q * q): return False
    S1 = (s - N * t0) // q; S2 = (Q - 2 * t0 * s + N * t0 * t0) // (q * q); m = S1 // N
    var = S2 - 2 * m * S1 + N * m * m
    return (S2 - S1) % 2 == 0 and S1 - N * m <= var and var != 0

def box_ok(N, q, s, Q, t0, c):
    if not moments_ok(N, q, s, Q, t0): return False
    S1 = (s - N * t0) // q; S2 = (Q - 2 * t0 * s + N * t0 * t0) // (q * q)
    lo, hi = -((c + t0) // q), (c - t0) // q
    return S2 <= (lo + hi) * S1 - N * lo * hi

def kills(r, c):
    """Literal CmCert.Kills."""
    ms, ds, ps = r["ms"], c["ds"], c["ps"]
    if not all(m > 0 for m in ms): return "ms<=0"
    if len(ds) != len(ms) or any(m % d for d, m in zip(ds, ms)): return "Dvds"
    H = math.prod(ds)
    if H <= 1: return "trivial H"
    if r["k"] == r["lam"]: return "k=lam"
    for p, i, j in ps:
        if not isprime(p) or i <= 0 or any((p ** i + 1) % d for d in ds) or H % p == 0 \
           or (r["k"] - r["lam"]) % (p ** (2 * j)): return f"prime cond {p,i,j}"
    if len({p for p, _, _ in ps}) != len(ps): return "pairwise"
    v = math.prod(ms)
    if c["s"] ** 2 != r["k"] + r["lam"] * (v - 1): return "s"
    q = math.prod(p ** j for p, _, j in ps)
    cc = v // H; Q = r["k"] + r["lam"] * (cc - 1)
    for sp in (c["s"], -c["s"]):
        for t in range(q):
            if box_ok(H, q, sp, Q, t, cc): return f"box passes s'={sp} t={t}"
    return None

def divs(m): return [d for d in range(1, m + 1) if m % d == 0]
def pfac(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0: f[d] = f.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def sc_exp(p, e):
    """least i>0 with p^i = -1 mod e, None if none"""
    if math.gcd(p, e) != 1: return None
    x = 1
    for i in range(1, 2 * e + 2):
        x = x * p % e
        if (x + 1) % e == 0: return i
    return None

def search(r, maxq=20000, need_multi=True):
    v, k, lam, ms = r["v"], r["k"], r["lam"], r["ms"]
    n = k - lam; S = k + lam * (v - 1)
    if n == 0 or S < 0 or math.isqrt(S) ** 2 != S: return None
    s = math.isqrt(S); fn = pfac(abs(n))
    seen = set()
    for ds in itertools.product(*[divs(m) for m in ms]):
        H, e = math.prod(ds), math.lcm(*ds)
        if H == 1 or (H, e) in seen: continue
        seen.add((H, e))
        good = [(p, sc_exp(p, e), a // 2) for p, a in fn.items() if a >= 2 and H % p and sc_exp(p, e)]
        if len(good) < (2 if need_multi else 1): continue
        cc = v // H; Q = k + lam * (cc - 1)
        for rsz in range(len(good), (1 if need_multi else 0), -1):
            for sub in itertools.combinations(good, rsz):
                q = math.prod(p ** j for p, _, j in sub)
                if q > maxq: continue
                if not any(box_ok(H, q, sp, Q, t, cc) for sp in (s, -s) for t in range(q)):
                    return list(ds), list(sub), s
    return None

if __name__ == "__main__":
    R = rows()
    L, nparen = lean_rows()
    print("lean rows parsed", len(L), "row tuples in file", nparen)
    objtxt = (P / "objects/_objects.md").read_text(encoding="utf-8")
    bad = 0
    for c in L:
        r = R[c["id"]]
        prob = []
        if r["ms"] != c["ms"] or r["k"] != c["k"] or r["lam"] != c["lam"] or r["v"] != math.prod(c["ms"]): prob.append("data mismatch")
        if r["status"] != "open": prob.append("status " + r["status"])
        if re.search(rf"\| N{c['id']} \|", objtxt): prob.append("has object")
        kres = kills(c, c)
        if kres: prob.append("Kills fails: " + kres)
        if prob: bad += 1; print("N%d" % c["id"], prob)
    print("rows with problems:", bad)
    ids = sorted(c["id"] for c in L)
    print("distinct ids", len(set(ids)))
    st = [l.split("\t") for l in (P / "scratch/settle-round4.tsv").read_text(encoding="utf-8").splitlines()]
    sn = sorted(int(x[0][1:]) for x in st if x[1] == "none")
    print("settle none == lean ids:", sn == ids)
    for x in st:
        if x[1] == "none":
            i = int(x[0][1:]); ch = [ci for ci, c in enumerate(L) if c["id"] == i][0] // 40 + 1
            if x[3] != f"SignedDifferenceSets.compositeModulusRows{ch}_not_hasSDS": print("chunk name mismatch", x)
    if "--search" in sys.argv:
        found = {}
        for i, r in R.items():
            res = search(r)
            if res: found[i] = res
        op = {i for i in found if R[i]["status"] == "open"}
        print("own search: kills", len(found), "open", len(op))
        print("by status:", {s: sum(1 for i in found if R[i]["status"] == s) for s in set(R[i]["status"] for i in found)})
        for i in sorted(found):
            if R[i]["status"] == "exists": print("KILLS EXISTS ROW N%d" % i, R[i], found[i])
        print("open killed, not in lean:", sorted(op - set(ids))[:50], len(op - set(ids)))
        print("lean, not killed by own:", sorted(set(ids) - set(found)))
