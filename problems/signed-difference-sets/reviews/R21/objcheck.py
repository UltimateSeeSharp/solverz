# Check C22 and each intermediate claim of its proof on every known SDS (objects/ and E10 `found`).
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import glob, itertools, math, re, sys
from cyc import val, vpi, conj, mul
P = "problems/signed-difference-sets/"

def load_objects():
    out = []
    for f in sorted(glob.glob(P + "objects/O*.txt")):
        L = [l.split() for l in open(f) if l.strip()]
        hdr = L[0]
        orders = [int(x) for x in hdr[0][1:].split("xC")]
        vkl = tuple(int(x) for x in hdr[1].strip("()").split(","))
        D = {}
        for row in L[1:]:
            coords = tuple(int(x) for x in row[:-1]); sg = row[-1]
            assert len(coords) == len(orders), (f, row)
            D[coords] = 1 if sg == "+" else -1
        out.append((f.split("/")[-1].split("\\")[-1], orders, vkl, D))
    for l in open(P + "scratch/e10.out"):
        w = l.split()
        if len(w) > 2 and w[2] == "found":
            m = re.match(r"SDS\((-?\d+),(-?\d+),(-?\d+),\[([\d,]+)\]\)", w[1])
            orders = [int(x) for x in m[4].split(",")]
            D = {}
            for tok in w[7:]:
                coords = tuple(int(x) for x in tok[:-1].split(".")); D[coords] = 1 if tok[-1] == "+" else -1
            out.append((w[0], orders, (int(m[1]), int(m[2]), int(m[3])), D))
    return out

def check_sds(orders, vkl, D):
    v, k, lam = vkl
    assert math.prod(orders) == v and len(D) == k
    G = list(itertools.product(*[range(o) for o in orders]))
    add = lambda x, y: tuple((a + b) % o for a, b, o in zip(x, y, orders))
    for g in G:
        if any(g):
            c = sum(s * D.get(add(x, g), 0) for x, s in D.items())
            if c != lam:
                return False
    return True

def primes(x):
    return [p for p in range(2, x + 1) if x % p == 0 and all(p % d for d in range(2, int(p ** .5) + 1))]

def c22_check(name, orders, vkl, D, log):
    v, k, lam = vkl
    n = k - lam; s1 = sum(D.values()); assert s1 * s1 == n + lam * v
    bad = []
    for p in primes(v):
        qs = [p ** val(o, p) for o in orders]; qs = [q for q in qs]  # p-parts (1 allowed)
        t = val(v, p); e = val(n, p)
        H = list(itertools.product(*[range(q) for q in qs]))
        a = {h: 0 for h in H}
        for x, sg in D.items():
            a[tuple(xi % q for xi, q in zip(x, qs))] += sg
        a0 = a[tuple(0 for _ in qs)]
        q = max(qs); J = val(q, p); Phi = (q // p) * (p - 1)
        # parameter-form statement
        if p == 2:
            mm = math.isqrt(n)
            ok_sq = mm * mm == n
            if not ok_sq: bad.append((p, "n not square")); continue
            w = val(mm, 2)
            if min(val(s1, 2), t) != min(w, t): bad.append((p, "C22 eq"))
        else:
            if val(s1, p) < min(t, (e + 1) // 2): bad.append((p, "C22 div"))
        if e == 0 and p > 2:
            log.append(f'{name} p={p} e=0 skipped chars'); continue
        # intermediate claims: characters c of H, values in Z[zeta_q]
        total = [0] * q; real_sum = 0; nr_pairs = 0; seen = set()
        for c in H:
            xc = [0] * q
            for h, ah in a.items():
                if ah:
                    ex = sum(ci * hi * (q // qi) for ci, hi, qi in zip(c, h, qs)) % q
                    xc[ex] += ah
            for i in range(q): total[i] += xc[i]
            if not any(c): continue
            vx = vpi(xc, q)
            if 2 * vx != Phi * e:
                bad.append((p, c, "v_pi(psi(a)) != Phi e/2", vx, Phi * e))
            negc = tuple((-ci) % qi for ci, qi in zip(c, qs))
            if negc == c:  # real character
                # value must be an integer: all coeffs on zeta^0 and zeta^{q/2}
                iv = xc[0] - (xc[q // 2] if q % 2 == 0 else 0)
                if any(xc[i] for i in range(q) if i not in (0, q // 2)) and p == 2:
                    bad.append((p, c, "real char non-integer?"))
                if p == 2:
                    if iv * iv != n: bad.append((p, c, "real value^2 != n", iv))
                    real_sum += iv
            elif p == 2 and c not in seen:
                seen.add(c); seen.add(negc)
                y = [xc[i] + conj(xc, q)[i] for i in range(q)]
                # order of psi = 2^j; check bound in own ring and big ring
                vy = vpi(y, q)
                if vy < Phi * (e // 2) + 1:
                    bad.append((p, c, "pair sum v_pi too small", vy, Phi * (e // 2)))
                nr_pairs += 1
        # sum over all characters = |H| a0
        from cyc import reduce
        red = reduce(total, q)
        if not (red[0] == p ** t * a0 and all(x == 0 for x in red[1:])):
            bad.append((p, "sum of chars != p^t a0", red[:3], p ** t * a0))
        if p == 2:
            snr = p ** t * a0 - s1 - real_sum
            w = val(math.isqrt(n), 2)
            if val(snr, 2) < w + 1: bad.append((p, "S_nr v2 too small", snr))
            if val(real_sum, 2) != w: bad.append((p, "real sum v2 != w", real_sum))
        log.append(f"{name} {orders} {vkl} p={p} t={t} e={e} s={s1} q={q} pairs={nr_pairs}")
    return bad

if __name__ == "__main__":
    objs = load_objects()
    if len(sys.argv) > 1 and sys.argv[1] == 'e10': objs = [o for o in objs if o[0].startswith('N')]
    log = []; allbad = []
    for name, orders, vkl, D in objs:
        if math.prod(orders) > 1000:
            ok = "skip-sds-check"
        else:
            ok = check_sds(orders, vkl, D)
        if ok is False:
            print("NOT AN SDS", name); continue
        b = c22_check(name, orders, vkl, D, log)
        print(name, orders, vkl, "sds" if ok is True else ok, "violations:", b, flush=True)
        allbad += b
    print("\n".join(log))
    print("TOTAL violations", len(allbad))
