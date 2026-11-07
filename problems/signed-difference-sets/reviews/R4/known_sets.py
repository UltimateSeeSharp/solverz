# Load every known SDS (Gordon Yes/All sets, the project's objects and found sets, and
# constructed difference sets), verify it, then check rule SC's lemma on every coordinatewise
# quotient: coset sums congruent mod p^j for p^(2j) | n, p not dividing |H|, p self-conjugate
# mod exp(H). Also: rule SC must not kill the parameters (indep.witnesses).
import sys, json, re, math, itertools, glob, collections
sys.path.insert(0, ".")
from indep import factor, selfconj, witnesses
import numpy as np
W = "problems/signed-difference-sets"
GORDON = "problems/signed-difference-sets/scratch/data/gordon/sds.json"
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

def as_array(shape, plus, minus):
    A = np.zeros(shape, dtype=np.int64)
    for s, els in ((1, plus), (-1, minus)):
        for g in els:
            g = (g,) if isinstance(g, int) else tuple(g)
            assert A[g] == 0; A[g] = s
    return A

def autocorr(A):
    F = np.fft.fftn(A)
    return np.rint(np.fft.ifftn(F * np.conj(F)).real).astype(np.int64)  # sum_x A(x) A(x+g)

def is_sds(A, k, lam):
    ac = autocorr(A); z = (0,) * A.ndim
    off = ac.copy(); off[z] = lam
    return int((A != 0).sum()) == k and ac[z] == k and bool((off == lam).all())

def check(name, shape, k, lam, A, stats, viol):
    v = math.prod(shape); n = k - lam
    if not is_sds(A, k, lam):
        stats["not_sds"] += 1; viol.append(("NOT_SDS", name)); return
    stats["sets"] += 1
    if witnesses(v, k, lam, shape): viol.append(("KILLED", name))
    fn = factor(n) if n > 0 else {}
    for d in itertools.product(*[[x for x in range(1, m + 1) if m % x == 0] for m in shape]):
        h = math.prod(d)
        if h == 1: continue
        m = math.lcm(*d)
        a = np.zeros(d, dtype=np.int64)
        idx = np.indices(shape).reshape(len(shape), -1)
        red = tuple(idx[i] % d[i] for i in range(len(shape)))
        np.add.at(a, red, A.reshape(-1))
        c = v // h
        assert np.abs(a).max() <= c
        for p, e in fn.items():
            if h % p == 0 or not selfconj(p, m): continue
            if e % 2: viol.append(("ODD", name, d, p, e)); continue
            q = p ** (e // 2); stats["tests"] += 1; stats["j>=2"] += (e >= 4); stats["c=1"] += (c == 1)
            if ((a - a.flat[0]) % q != 0).any(): viol.append(("CONG", name, d, p, e // 2, a.tolist()))

def gordon_sets():
    for key, e in json.load(open(GORDON, encoding="utf-8")).items():
        if e["status"] not in ("Yes", "All"): continue
        v, k, lam = map(int, KEY.fullmatch(key).groups()[:3]); shape = [int(x) for x in KEY.fullmatch(key).group(4).split(",")]
        for i, (P, N) in enumerate(e.get("sets", [])):
            g0 = (P + N)[0]
            if not isinstance(g0, int) and len(g0) != len(shape):  # undocumented representation
                sh2 = [max(g[t] for g in P + N) + 1 for t in range(len(g0))]
                assert math.prod(sh2) == v, key
                print("note: element format", sh2, "for", key); shape = sh2
            yield f"G:{key}#{i}", shape, k, lam, as_array(shape, P, N)

def parse_tokens(shape, toks):
    plus, minus = [], []
    for t in toks:
        g = [int(x) for x in t[:-1].split(".")]
        (plus if t[-1] == "+" else minus).append(g)
    return plus, minus

def project_sets():
    seen = set()
    for f in ["e6", "e7", "r3", "r4"]:
        for line in open(f"{W}/scratch/{f}.out", encoding="utf-8"):
            t = line.split()
            if " yes " not in line: continue
            ki = next(i for i, x in enumerate(t) if x.startswith("SDS("))
            key = t[ki]; v, k, lam = map(int, KEY.fullmatch(key).groups()[:3]); shape = [int(x) for x in KEY.fullmatch(key).group(4).split(",")]
            toks = [x for x in t[ki + 1:] if x[-1] in "+-" and x[0].isdigit()]
            sig = (key, tuple(toks))
            if sig in seen: continue
            seen.add(sig)
            yield f"P:{f}:{key}", shape, k, lam, as_array(shape, *parse_tokens(shape, toks))
    for f in sorted(glob.glob(f"{W}/objects/O*.txt")):
        L = open(f, encoding="utf-8").read().split("\n")
        hdr = L[0].split(); shape = [int(x) for x in hdr[0][1:].split("xC")]
        v, k, lam = map(int, hdr[1].strip("()").split(","))
        plus = [[int(x) for x in l.split()[:-1]] for l in L[1:] if l.strip() and l.split()[-1] == "+"]
        minus = [[int(x) for x in l.split()[:-1]] for l in L[1:] if l.strip() and l.split()[-1] == "-"]
        yield f"O:{f[-7:]}", shape, k, lam, as_array(shape, plus, minus)

if __name__ == "__main__":
    import constructions
    stats, viol = collections.Counter(), []
    for src in (gordon_sets(), project_sets(), constructions.all_sets()):
        for name, shape, k, lam, A in src:
            check(name, shape, k, lam, A, stats, viol)
            stats[name[:2]] += 1
    print(dict(stats)); print("violations:", len(viol)); [print(x) for x in viol]
