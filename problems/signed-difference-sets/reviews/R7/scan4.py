"""All signed unions of order-4 cyclotomic classes and {0} in (GF(q),+), q = 1 mod 4 prime power <= 500
(HCG Sec 5's families, and Paley-type e = 2). Correlation is constant on classes (D is C0-invariant), so
it is checked at one representative per class; every hit is rechecked on all g. Prints hits' db status."""
import csv, itertools, json, sys
from build import GF, prime_divisors
from sdscheck import check_direct

db = json.load(open(sys.argv[1]))
inst = {r["key"]: r for r in csv.DictReader(open(sys.argv[2], encoding="utf-8"))}


def prime_power(v):
    ps = prime_divisors(v)
    if len(ps) != 1:
        return None
    e, x = 0, v
    while x > 1:
        x //= ps[0]
        e += 1
    return ps[0], e


def add(a, b, p):
    return tuple((x + y) % p for x, y in zip(a, b))


for q in range(5, 501, 4):
    pe = prime_power(q)
    if not pe:
        continue
    p, e = pe
    F = GF(p, e)
    w = F.prim
    f = (q - 1) // 4
    pw = [F.one]
    for _ in range(q - 2):
        pw.append(F.mul(pw[-1], w))
    C = [[pw[4 * j + i] for j in range(f)] for i in range(4)]
    reps = [pw[i] for i in range(4)]
    seen = set()
    for signs in itertools.product((-1, 0, 1), repeat=5):
        if all(s == 0 for s in signs) or signs in seen:
            continue
        seen.add(tuple(-s for s in signs))  # D and -D are the same SDS type
        D = {}
        for i in range(4):
            if signs[i]:
                for x in C[i]:
                    D[x] = signs[i]
        if signs[4]:
            D[F.zero] = signs[4]
        cs = {sum(c * D.get(add(x, g, p), 0) for x, c in D.items()) for g in reps}
        if len(cs) != 1:
            continue
        lam = cs.pop()
        k = len(D)
        if k == q and lam in (q, q - 4):  # Gordon's excluded trivial cases
            continue
        ok, _ = check_direct(D, (p,) * e, k, lam)
        assert ok, (q, signs)
        key = f"SDS({q},{k},{lam},[{','.join([str(p)] * e)}])"
        d = db.get(key)
        r = inst.get(key)
        st = d["status"] if d else "ABSENT"
        flag = "   <-- Open" if st == "Open" else ""
        print(f"q={q} signs(C0..C3,0)={signs}: {key} db={st} '{d['comment'] if d else ''}' "
              f"csv={r['id'] + ' ' + r['status'] if r else '-'}{flag}", flush=True)
