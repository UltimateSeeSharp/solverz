# For every instances.csv row with a Lean theorem: does the Lean statement's group, k, lam
# equal the table entry (key)? Individual theorems: parse the statement. List theorems: find the
# row's entry <id, ms, k, lam> in the list the theorem quantifies over.
import csv, re, sys, os, collections
root = sys.argv[1]
L = root + "/lean/SignedDifferenceSets"
files = {}
# REACH: only modules imported (transitively) by the library root
seen=set(); stack=['SignedDifferenceSets']
while stack:
    mod=stack.pop()
    if mod in seen: continue
    seen.add(mod)
    q=os.path.join(root,'lean',*mod.split('.'))+'.lean'
    if os.path.exists(q):
        stack += re.findall(r'^(?:public )?import (SignedDifferenceSets\S*)', open(q,encoding='utf-8').read(), re.M)
for dp, _, fs in os.walk(L):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(dp, f)
            mod = os.path.relpath(p, root + "/lean")[:-5].replace(os.sep, ".")
            if mod in seen: files[p] = open(p, encoding="utf-8").read()
def ns_of(text):
    m = re.findall(r"^namespace (\S+)", text, re.M); return m[0] if m else ""
# theorem index: full name -> (file, statement)
thm = {}
for p, t in files.items():
    ns = ns_of(t)
    for m in re.finditer(r"^theorem (\S+)(.*?):=", t, re.M | re.S):
        thm[ns + "." + m.group(1)] = (p, " ".join(m.group(2).split()))
# list defs: (ns, name) -> {id: (ms, k, lam)}
lists = {}
for p, t in files.items():
    ns = ns_of(t)
    for m in re.finditer(r"^def (\S+) : List \(?Row[^=]*:= \[(.*?)\]\s*$", t, re.M | re.S):
        body = m.group(2)
        d = {}
        for e in re.finditer(r"⟨(\d+), \[([\d, ]*)\], (\d+), (-?\d+)⟩", body):
            d.setdefault(int(e.group(1)), []).append(([int(x) for x in e.group(2).split(",") if x.strip()], int(e.group(3)), int(e.group(4))))
        lists[(ns, m.group(1))] = d
def parse_group(s):
    s = s.strip()
    if s.startswith("Grp"):
        return [int(x) for x in re.search(r"\[([\d, ]*)\]", s).group(1).split(",")]
    parts = [x.strip() for x in s.split("×")]
    out = []
    for q in parts:
        m = re.fullmatch(r"ZMod (\d+)", q)
        if not m: return None
        out.append(int(m.group(1)))
    return out
rows = list(csv.DictReader(open(root + "/instances.csv", encoding="utf-8")))
stats = collections.Counter(); bad = []
for r in rows:
    if not r["lean"]: continue
    m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", r["key"])
    v, k, lam = int(m.group(1)), int(m.group(2)), int(m.group(3)); ms = [int(x) for x in m.group(4).split(",")]
    if v != eval("*".join(map(str, ms))): bad.append((r["id"], "v!=prod", r["key"]))
    inv = all(ms[i + 1] % ms[i] == 0 for i in range(len(ms) - 1)) and all(x > 1 for x in ms)
    if not inv: stats["key not invariant-factor form"] += 1
    name = r["lean"]
    if name not in thm: bad.append((r["id"], "no theorem", name)); continue
    p, st = thm[name]
    mi = re.search(r"(¬ )?@?HasSDS \((.*?)\) (?:_ inst )?(\d+) (-?\d+)$", st)
    if mi and "x.1" not in st and "x.ms" not in st:
        g = parse_group(mi.group(2))
        want_neg = r["status"] == "none"
        ok = g == ms and int(mi.group(3)) == k and int(mi.group(4)) == lam and (bool(mi.group(1)) == want_neg)
        stats["individual " + ("ok" if ok else "BAD")] += 1
        if not ok: bad.append((r["id"], r["key"], r["status"], st[:120]))
        if g is None:
            stats["individual other form"] += 1
        continue
    ml = re.search(r"∈ (\S+)\)", st)
    ns = name.rsplit(".", 1)[0]
    lname = ml.group(1) if ml else None
    key = (ns, lname)
    if key not in lists:
        # MaRows: theorem in All.lean refers to partNN in the same namespace
        bad.append((r["id"], "list not found", name, lname)); continue
    ent = lists[key].get(int(r["id"][1:]))
    if not ent: bad.append((r["id"], "id not in list", name)); stats["list missing"] += 1; continue
    ok = all(e == (ms, k, lam) for e in ent)
    stats["list " + ("ok" if ok else "BAD")] += 1
    if not ok: bad.append((r["id"], r["key"], ent))
    if r["status"] != "none": bad.append((r["id"], "list theorem but status", r["status"]))
print(stats); print(len(bad)); print(bad[:20])
