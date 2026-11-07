"""C23's congruence on real SDSs: for every stored object and every quotient H with qualifying primes,
the coset sums agree mod q = prod p^j."""
import sys, pathlib, math, itertools, re
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from c23_check import pfac, divs, sc_exp
P = pathlib.Path(__file__).resolve().parents[3]
tested = multi = bad = 0
for f in sorted((P / "objects").glob("O*.txt"), key=lambda p: int(p.stem[1:])):
    first, *rest = f.read_text(encoding="utf-8").splitlines()
    m = re.search(r"\((\d+),\s*(\d+),\s*(-?\d+)\)", first)
    ms = [int(x) for x in re.findall(r"C(\d+)", first.split()[0])]
    if not m or not ms: continue
    v, k, lam = map(int, m.groups()); n = k - lam
    if n == 0: continue
    D = {}
    for l in rest:
        if l.strip():
            *cs, s = l.split(); D[tuple(map(int, cs))] = 1 if s == "+" else -1
    fn = pfac(abs(n))
    for ds in itertools.product(*[divs(x) for x in ms]):
        H, e = math.prod(ds), math.lcm(*ds)
        if H == 1: continue
        good = [(p, a // 2) for p, a in fn.items() if a >= 2 and H % p and sc_exp(p, e)]
        if not good: continue
        q = math.prod(p ** j for p, j in good)
        a = {}
        for x, s in D.items():
            h = tuple(c % d for c, d in zip(x, ds)); a[h] = a.get(h, 0) + s
        vals = [a.get(h, 0) for h in itertools.product(*[range(d) for d in ds])]
        tested += 1; multi += len(good) >= 2
        if any((x - vals[0]) % q for x in vals): bad += 1; print("VIOLATION", f.name, ds, good, vals[:10])
print("object/quotient pairs tested:", tested, "with >=2 primes:", multi, "violations:", bad)
