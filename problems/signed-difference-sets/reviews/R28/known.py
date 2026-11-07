"""Known sets (objects O*, Gordon's stored sets) with 4 | n and an even factor: verify the SDS, then check (a), (b) on
quotients Z_2^j x K (qcheck.run_set: exhaustive when small, else sampled linear maps)."""
import json, re, math, sys, collections
from pathlib import Path
import numpy as np
from qcheck import run_set

ROOT = Path(__file__).resolve().parents[3]
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")

def verify(ms, D):
    """Vectorised SDS check; returns (k, lam) or None."""
    shape = tuple(ms); A = np.zeros(shape, dtype=np.int64)
    for e, s in D.items(): A[e] = s
    k = int((A != 0).sum())
    # autocorrelation via FFT-free direct roll over each nonzero shift is O(v^2); use FFT for speed
    F = np.fft.fftn(A); ac = np.real(np.fft.ifftn(F * np.conj(F)))
    ac = np.rint(ac).astype(np.int64).ravel()
    off = ac[1:]
    if len(off) and not (off == off[0]).all(): return None
    return k, (int(off[0]) if len(off) else 0)

def sets():
    for f in sorted((ROOT / "objects").glob("O*.txt"), key=lambda p: int(p.stem[1:])):
        L = f.read_text().split("\n"); head = L[0].split()
        ms = [int(x[1:]) for x in head[0].split("x")]; v, k, lam = map(int, head[1].strip("()").split(","))
        D = {}
        for l in L[1:]:
            if l.strip():
                p = l.split(); D[tuple(int(x) for x in p[:-1])] = 1 if p[-1] == "+" else -1
        yield f.stem, ms, k, lam, D
    data = json.load(open(ROOT / "scratch/data/gordon/sds.json", encoding="utf-8"))
    for key, E in data.items():
        if "sets" not in E: continue
        v, k, lam, ms = KEY.fullmatch(key).groups(); k, lam = int(k), int(lam); ms = [int(x) for x in ms.split(",")]
        for t, S in enumerate(E["sets"]):
            D = {}
            for sgn, part in ((1, S[0]), (-1, S[1])):
                for x in part:
                    e = (x,) if isinstance(x, int) else tuple(x)
                    D[e] = sgn
            yield f"{key}#{t}", ms, k, lam, D

if __name__ == "__main__":
    tot = 0; st = collections.Counter(); bad = []; badsds = []; cs = collections.Counter()
    for name, ms, k, lam, D in sets():
        if any(len(e) != len(ms) for e in D): badsds.append((name, 'dim', k, lam)); continue
        r = verify(ms, D)
        if r != (k, lam): badsds.append((name, r, k, lam)); continue
        n = k - lam
        if n <= 0 or n % 4 or all(m % 2 for m in ms): continue
        tot += 1
        for shape, sc, oa, ob, c, forms in run_set(ms, D, k, lam, exhaustive_limit=3000, samples=40):
            st[(sc, oa, ob)] += 1
            if sc: cs[c] += 1
            if sc and not (oa and ob): bad.append((name, ms, k, lam, shape, forms, oa, ob))
        print(name, ms, k, lam, flush=True)
    print("sets with 4|n and even factor:", tot, "checks (selfconj, a, b):", dict(st))
    print("c values hit:", sorted(cs.items()))
    print("not an SDS as stored:", badsds[:10], len(badsds))
    print("violations:", len(bad)); [print(" ", b) for b in bad[:10]]
