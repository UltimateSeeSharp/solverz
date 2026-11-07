"""Refuter's independent check: parse each claimed set, build D: G -> {-1,0,1} on the key's
invariant-factor group G = Z_m1 x ... x Z_mr (first factor first), test IsSDS literally."""
import sys, re, itertools, ast
WT = "problems/signed-difference-sets"
MS = "problems/signed-difference-sets/scratch"

def parse_key(key):
    m = re.fullmatch(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)", key)
    v, k, lam = int(m[1]), int(m[2]), int(m[3])
    f = tuple(int(x) for x in m[4].split(","))
    return v, k, lam, f

def check(key, entries):
    """entries: list of (coord tuple, sign). Returns a report string."""
    v, k, lam, f = parse_key(key)
    prod = 1
    for m in f: prod *= m
    errs = []
    if prod != v: errs.append(f"prod(f)={prod}!=v")
    # invariant factors must divide successively
    for a, b in zip(f, f[1:]):
        if b % a: errs.append(f"not invariant factors {f}")
    D = {}
    for c, s in entries:
        if len(c) != len(f): errs.append(f"arity {c}"); continue
        if any(not (0 <= x < m) for x, m in zip(c, f)): errs.append(f"out of range {c}")
        if c in D: errs.append(f"duplicate {c}")
        if s not in (1, -1): errs.append(f"bad sign {s}")
        D[c] = s
    G = list(itertools.product(*[range(m) for m in f]))
    kk = sum(1 for g in G if D.get(g, 0) != 0)
    vals = {}
    for g in G:
        if not any(g): continue
        t = 0
        for x, sx in D.items():
            y = tuple((a + b) % m for a, b, m in zip(x, g, f))
            t += sx * D.get(y, 0)
        vals[t] = vals.get(t, 0) + 1
    s = sum(D.values())
    ok = (not errs) and kk == k and set(vals) == {lam}
    return f"{key}: k={kk} (want {k}), sum={s}, shift values {vals} (want {{{lam}}}), errs={errs[:3]} -> {'OK' if ok else 'FAIL'}"

def coords_tokens(toks):
    out = []
    for t in toks:
        sign = 1 if t[-1] == '+' else -1 if t[-1] == '-' else None
        out.append((tuple(int(x) for x in t[:-1].split('.')), sign))
    return out

def from_e9(path, ids):
    res = {}
    for line in open(path):
        p = line.split()
        if p and p[0] in ids and p[3] == 'yes':
            res[p[0]] = (p[1], coords_tokens(p[6:]))
    return res

def from_r4(path, ids):
    res = {}
    for line in open(path):
        p = line.split()
        if p and p[0] in ids and p[2] == 'yes':
            res[p[0]] = (p[1], coords_tokens(p[5:]))
    return res

def from_O(path, key):
    lines = open(path).read().split('\n')
    ent = []
    for l in lines[1:]:
        p = l.split()
        if not p: continue
        ent.append(((int(p[0]), int(p[1])), 1 if p[2] == '+' else -1 if p[2] == '-' else None))
    return {"N35840": (key, ent)}, lines[0]

if __name__ == "__main__":
    allres = {}
    allres.update(from_e9(MS + "/e8/e9-200.out", {"N286", "N638", "N130", "N132", "N139", "N170", "N169"}))
    r4 = from_r4(WT + "/scratch/r4.out", {"N127", "N128", "N129", "N130", "N132", "N137", "N139", "N169", "N170"})
    e7 = from_r4(WT + "/scratch/e7.out", {"N131"})
    o12, hdr = from_O(WT + "/objects/O12.txt", "SDS(361,316,141,[19,19])")
    print("O12 header:", hdr)
    for src, d in [("e9-200", allres), ("r4", r4), ("e7", e7), ("O12", o12)]:
        for i, (key, ent) in sorted(d.items()):
            print(src, i, check(key, ent))
