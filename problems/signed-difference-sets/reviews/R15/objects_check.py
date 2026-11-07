# For every object O*.txt: check it is an SDS, compute every real character value chi(D) on G/2G,
# check chi(D)^2 = n, the h = 0 identity sum_chi chi(D) = 2^R a_0, and that C17 does not fire.
import itertools, math, re, sys
from pathlib import Path
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent)); from rows import rule, kills_closed
PF = Path(__file__).resolve().parents[3]
def load(p):
    lines = p.read_text().split("\n")
    g, par = re.match(r"(\S+) \((-?\d+),(-?\d+),(-?\d+)\)", lines[0]).groups()[0], \
        tuple(map(int, re.match(r"\S+ \((-?\d+),(-?\d+),(-?\d+)\)", lines[0]).groups()))
    fs = [int(x[1:]) for x in g.split("x")]
    D = {}
    for l in lines[1:]:
        if not l.strip(): continue
        *c, sg = l.split(); D[tuple(int(x) for x in c)] = 1 if sg == "+" else -1
    return fs, par, D
bad = 0
for p in sorted((PF / "objects").glob("O*.txt"), key=lambda q: int(q.stem[1:])):
    fs, (v, k, lam), D = load(p)
    assert math.prod(fs) == v and len(D) == k, p
    els = list(itertools.product(*[range(f) for f in fs]))
    for g in els[1:]:
        c = sum(sg * D.get(tuple((a + b) % f for a, b, f in zip(x, g, fs)), 0) for x, sg in D.items())
        assert c == lam, (p.name, g, c)
    ev = [i for i, f in enumerate(fs) if f % 2 == 0]; R = len(ev); n = k - lam
    sp = sum(D.values())
    info = f"{p.stem} {fs} ({v},{k},{lam}) R={R}"
    if R:
        vals = []
        for bits in itertools.product((0, 1), repeat=R):
            # chi(x) = (-1)^(sum bits_i x_{ev_i})
            val = sum(sg * (-1) ** sum(b * x[i] for b, i in zip(bits, ev)) for x, sg in D.items())
            vals.append(val)
            if any(bits): assert val * val == n, (p.name, bits, val, n)
        a0 = sum(sg for x, sg in D.items() if all(x[i] % 2 == 0 for i in ev))
        assert sum(vals) == (1 << R) * a0 and vals[0] == sp
        fired = rule(v, k, lam, fs)
        info += f" s'={sp} m={math.isqrt(n)} a0={a0} T={sum(vals[1:])//max(1,math.isqrt(n)) if n else '-'} fired={fired}"
        if fired is not None: bad += 1
    print(info)
print("objects where C17 fires:", bad)
