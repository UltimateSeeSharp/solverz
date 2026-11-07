"""Refuter's independent check of N17201 (256,154,90) and N735 (64,46,30) in C2^m (XOR).
Two independent SDS tests: (a) direct signed autocorrelation on every shift, written as the
Lean definition reads (sum_x D(x) D(x+g)); (b) Walsh-Hadamard: |D^(chi)|^2 = k - lam for chi != 1,
D^(1)^2 = k + lam (v-1). PDS parameters of P are counted directly."""
import itertools, numpy as np

def autocorr(D):
    v = len(D); return [sum(D[x] * D[x ^ g] for x in range(v)) for g in range(v)]

def fwht(a):
    a = np.array(a, dtype=np.int64); h = 1
    while h < len(a):
        for i in range(0, len(a), 2 * h):
            x = a[i:i+h].copy(); y = a[i+h:i+2*h].copy(); a[i:i+h] = x + y; a[i+h:i+2*h] = x - y
        h *= 2
    return a

def sds_check(D, k, lam):
    v = len(D); ac = autocorr(D)
    supp = sum(1 for x in D if x != 0)
    direct = supp == k and all(ac[g] == lam for g in range(1, v))
    W = fwht(D); spec = (W[1:] ** 2 == k - lam).all() and W[0] ** 2 == k + lam * (v - 1)
    return direct, bool(spec), supp, sorted(set(ac[1:]))

def pds_params(P, v):
    S = set(P); lam = set(); mu = set()
    for g in range(1, v):
        c = sum(1 for y in S if (y ^ g) in S)
        (lam if g in S else mu).add(c)
    return len(S), lam, mu

# ---- GF(256) with a different modulus than the note's 0x11D, found by search ----
def gf_mul(a, b, mod, deg):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> deg & 1: a ^= mod
    return r

def gf_pow(a, e, mod, deg):
    r = 1
    while e:
        if e & 1: r = gf_mul(r, a, mod, deg)
        a = gf_mul(a, a, mod, deg); e >>= 1
    return r

def is_irreducible(mod, deg):  # x^(2^deg) = x mod f and gcd conditions via brute: no root of any degree <= deg/2 factor
    # brute force: f has no factor of degree d <= deg/2
    for d in range(1, deg // 2 + 1):
        for g in range(1 << d, 1 << (d + 1)):
            # polynomial division mod 2
            r = mod
            while r.bit_length() >= g.bit_length():
                r ^= g << (r.bit_length() - g.bit_length())
            if r == 0: return False
    return True

mods = [m for m in range(0x101, 0x200, 2) if is_irreducible(m, 8)]
MOD = [m for m in mods if m not in (0x11D,)][3]   # an irreducible modulus, not the note's
print("GF(256) modulus used:", hex(MOD), "(note used 0x11d)")
# classes by the order-5 character x -> x^51 (independent of any primitive element / log table)
fifth = sorted({gf_pow(x, 51, MOD, 8) for x in range(1, 256)})
assert len(fifth) == 5 and all(gf_pow(w, 5, MOD, 8) == 1 for w in fifth)
cls = {x: fifth.index(gf_pow(x, 51, MOD, 8)) for x in range(1, 256)}
assert all(sum(1 for x in cls if cls[x] == i) == 51 for i in range(5))
ok_all = True
for chosen in itertools.combinations(range(5), 3):
    P = [x for x in range(1, 256) if cls[x] in chosen]
    k, lam, mu = pds_params(P, 256)
    D = [0] * 256; D[0] = -1
    for x in P: D[x] = 1
    direct, spec, supp, acs = sds_check(D, 154, 90)
    ok_all &= direct and spec and (k, lam, mu) == (153, {92}, {90})
    print(" classes", chosen, "P:", k, lam, mu, "| D SDS direct", direct, "spectral", spec, "support", supp, "autocorr", acs)
print("N17201 all 10:", ok_all)
# negative control: 2 classes (NL_16(6), lam'-mu = -4) must fail; 3 classes with identity +1 must fail
P = [x for x in range(1, 256) if cls[x] in (0, 1)]
D = [0] * 256; D[0] = -1
for x in P: D[x] = 1
print(" control 2 classes:", pds_params(P, 256), sds_check(D, 103, 42)[:2])
P = [x for x in range(1, 256) if cls[x] in (0, 1, 2)]
D = [0] * 256; D[0] = 1
for x in P: D[x] = 1
print(" control identity +1:", sds_check(D, 154, 90)[:2], sds_check(D, 154, 92)[:2])

# ---- N735: GF(4)^3, hyperoval found by search (not the note's conic+nucleus) ----
# GF(4) as polynomials over GF(2) mod x^2+x+1: 0,1,x=2,x+1=3
def m4(a, b): return gf_mul(a, b, 0b111, 2)
pts = []
for v in itertools.product(range(4), repeat=3):
    if v == (0, 0, 0): continue
    # normalise: first nonzero coordinate = 1
    lead = next(c for c in v if c)
    inv = next(i for i in range(1, 4) if m4(lead, i) == 1)
    w = tuple(m4(inv, c) for c in v)
    if w not in pts: pts.append(w)
assert len(pts) == 21
def det(p, q, r):
    t = lambda a, b, c: m4(m4(a, b), c)
    return (t(p[0], q[1], r[2]) ^ t(p[1], q[2], r[0]) ^ t(p[2], q[0], r[1]) ^
            t(p[2], q[1], r[0]) ^ t(p[1], q[0], r[2]) ^ t(p[0], q[2], r[1]))
hyperovals = [S for S in itertools.combinations(pts, 6)
              if all(det(*tr) for tr in itertools.combinations(S, 3))]
print("hyperovals in PG(2,4):", len(hyperovals))  # known: 168
def enc(v): return v[0] | v[1] << 2 | v[2] << 4
bad = 0
for S in hyperovals:
    T = {enc(tuple(m4(l, c) for c in p)) for p in S for l in (1, 2, 3)}
    P = [x for x in range(1, 64) if x not in T]
    D = [0] * 64; D[0] = -1
    for x in P: D[x] = 1
    good = pds_params(sorted(T), 64) == (18, {2}, {6}) and pds_params(P, 64) == (45, {32}, {30}) \
        and sds_check(D, 46, 30)[:2] == (True, True)
    bad += not good
print("N735: hyperovals failing (T2*(O) PDS / complement PDS / SDS):", bad, "of", len(hyperovals))
S = hyperovals[0]
T = {enc(tuple(m4(l, c) for c in p)) for p in S for l in (1, 2, 3)}
P = [x for x in range(1, 64) if x not in T]
D = [0] * 64; D[0] = -1
for x in P: D[x] = 1
print(" first hyperoval", S, "P:", pds_params(P, 64), "D:", sds_check(D, 46, 30))
# negative control: a 6-arc that is not a hyperoval (one collinear triple) must fail
arc = next(S for S in itertools.combinations(pts, 6)
           if 0 < sum(1 for tr in itertools.combinations(S, 3) if det(*tr) == 0) <= 2)
T = {enc(tuple(m4(l, c) for c in p)) for p in arc for l in (1, 2, 3)}
D = [0] * 64; D[0] = -1
for x in range(1, 64):
    if x not in T: D[x] = 1
print(" control non-hyperoval:", sds_check(D, 46, 30)[:2])
