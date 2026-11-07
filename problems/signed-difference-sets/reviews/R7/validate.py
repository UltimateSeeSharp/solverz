"""Validate sdscheck on every set stored in sds.json with v <= VMAX, and on mutated sets."""
import json, random, sys
from sdscheck import check_direct, check_fft

SRC = sys.argv[1]
VMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 120
db = json.load(open(SRC))
random.seed(1)
acc = rej_ok = tot = 0
fails = []
skipped = []
for key, e in db.items():
    if "sets" not in e:
        continue
    head, grp = key[4:-2].split(",[")
    v, k, lam = map(int, head.split(","))
    mods = tuple(e["G_rep"]) if "G_rep" in e else tuple(map(int, grp.split(",")))
    if v > VMAX:
        continue
    for st in e["sets"][:1]:
        P, N = st
        norm = lambda x: tuple(x) if isinstance(x, list) else (x,)
        D = {norm(x): 1 for x in P}
        for x in N:
            D[norm(x)] = -1
        if any(len(x) != len(mods) or any(not 0 <= a < m for a, m in zip(x, mods)) for x in D):
            skipped.append(key); continue
        tot += 1
        ok1, _ = check_direct(D, mods, k, lam)
        ok2, _ = check_fft(D, mods, k, lam)
        if ok1 and ok2:
            acc += 1
        else:
            fails.append((key, ok1, ok2))
        # mutation: flip one sign; must be rejected unless still an SDS by accident
        x = random.choice(list(D))
        D2 = dict(D); D2[x] = -D2[x]
        r1, _ = check_direct(D2, mods, k, lam)
        r2, _ = check_fft(D2, mods, k, lam)
        if not r1 and not r2:
            rej_ok += 1
        elif r1 != r2:
            fails.append((key, "mutant disagree", r1, r2))
print(f"stored sets checked {tot}, accepted {acc}, flipped-sign mutants rejected {rej_ok}")
print("skipped (encoding not the key factors)", skipped)
print("fails", fails[:10], len(fails))
