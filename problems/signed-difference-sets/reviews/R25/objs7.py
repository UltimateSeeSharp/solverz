# Part 1: every object O1..O70: re-verify as SDS (FFT autocorrelation), then test C22's p = 2 equality
# on its Sylow 2-quotient: n = m^2, w = v2(m) < t => 2^(w+1) does not divide s (the actual sign sum).
import re, glob, os, numpy as np
from math import isqrt
def v2(x):
    x = abs(x); c = 0
    while x % 2 == 0: x //= 2; c += 1
    return c
out = []
for f in sorted(glob.glob("../../../objects/O*.txt"), key=lambda p: int(re.findall(r"O(\d+)", p)[-1])):
    lines = open(f, encoding="utf-8").read().strip().split("\n")
    g = re.match(r"(\S+) \((\d+),(\d+),(-?\d+)\)", lines[0]); ms = [int(x) for x in g[1].replace("C", "").split("x")]
    v, k, lam = int(g[2]), int(g[3]), int(g[4])
    A = np.zeros(ms, dtype=np.int64)
    for ln in lines[1:]:
        p = ln.split()
        if not p: continue
        A[tuple(int(x) for x in p[:-1])] = 1 if p[-1] == "+" else -1
    name = os.path.basename(f)[:-4]
    if v <= 5000:
        F = np.fft.fftn(A); ac = np.rint(np.fft.ifftn(F * np.conj(F)).real).astype(np.int64).ravel()
        ok = int((A != 0).sum()) == k and ac[0] == k and np.all(ac[1:] == lam)
    else: ok = None
    s = int(A.sum()); n = k - lam; t = v2(v); m = isqrt(n) if n > 0 else 0
    if t == 0: verdict = "v odd"
    elif m * m != n: verdict = "VIOLATION n not square"
    else:
        w = v2(m)
        if w >= t: verdict = f"w={w}>=t={t}, untested"
        else: verdict = f"w={w}<t={t}, v2(s)={v2(s) if s else 'inf'}" + (" VIOLATION" if s % 2 ** (w + 1) == 0 else " ok")
    out.append(f"{name} {ms} ({v},{k},{lam}) sds={ok} s={s}: {verdict}")
print("\n".join(out))
