"""Known sets (rule-sc's 683 verified + project objects) against the theorems behind A3, A5, A7:
A3: parity lemma #{x in Z: x+g in Z} = v + lam (mod 2) for all g != 0, and the rule must not fire.
A5: gcd(v,n)=1 => some translate of D or -D is M-invariant; the centroid-normalised translate is.
A7: every coordinatewise quotient H != 1, gcd(|H|,n)=1: some translate of a or -a is M_H-invariant;
    the centroid-normalised translate is. Also: is the set's (v,k,lam,iso type) among the kills?"""
import sys, math, itertools, glob, collections, ast; sys.path.insert(0, '.')
from common import *
sys.path.insert(0, RSC)
import numpy as np
import known_sets, constructions
def gens(M, e):
    G = []; H = {1 % e}
    for t in sorted(M):
        if t in H: continue
        G.append(t); H2 = set(H); fr = list(H)
        while fr:
            y = fr.pop(); 
            for g in G:
                z = y * g % e
                if z not in H2: H2.add(z); fr.append(z)
        H = H2
    assert H == set(M)
    return G
def invariant_translate(A, shape, M):
    """Return (#translates g with A(x-g) M-invariant, centroid-normalised translate invariant?)."""
    v = A.size; els = elements(shape); idx = {g: i for i, g in enumerate(els)}; e = math.lcm(*shape)
    perms = [np.array([idx[tuple(t * a % m for a, m in zip(g, shape))] for g in els]) for t in gens(M, e)]
    ax = tuple(range(len(shape))); good = 0
    for g in els:
        B = np.roll(A, g, axis=ax).reshape(-1)
        if all((B[P] == B).all() for P in perms): good += 1
    flat = A.reshape(-1); s = int(flat.sum())
    xi = tuple(int(sum(int(flat[i]) * els[i][j] for i in range(v))) % shape[j] for j in range(len(shape)))
    cen = None
    if math.gcd(abs(s), e) == 1:
        sinv = [pow(s % m, -1, m) if m > 1 else 0 for m in shape]
        g = tuple((-xi[j] * sinv[j]) % shape[j] for j in range(len(shape)))
        B = np.roll(A, g, axis=ax).reshape(-1)
        cen = all((B[P] == B).all() for P in perms)
    return good, cen
def kill_lists():
    oe = {l.split()[1] for p in glob.glob(IDEA + '/oe_*.out') for l in open(p) if l.split()[3] == 'none'}
    a3 = {l.split()[1] for l in open(IDEA + '/sp_hits.txt')}
    a7 = set()
    for p in glob.glob(IDEA + '/mc_*.out') + glob.glob(IDEA + '/mcb_*.out'):
        for l in open(p):
            x = l.split(None, 2)
            if ast.literal_eval(x[2].strip())[0] == 'KILL': a7.add(x[1])
    T = lambda key: (parse_key(key)[:3], invariant_type(parse_key(key)[3]))
    return {name: {T(k) for k in s} for name, s in (('A5', oe), ('A3', a3), ('A7', a7))}
if __name__ == '__main__':
    KL = kill_lists(); st = collections.Counter(); bad = []
    srcs = (known_sets.gordon_sets(), known_sets.project_sets(), constructions.all_sets())
    for src in srcs:
        for name, shape, k, lam, A in src:
            shape = list(shape); A = np.asarray(A).reshape(shape)
            if not known_sets.is_sds(A, k, lam): st['not_sds'] += 1; continue
            st['sets'] += 1; v = A.size; n = k - lam; d = v - k
            key = ((v, k, lam), invariant_type(shape))
            for nm, s in KL.items():
                if key in s: bad.append((nm + '_KILLS_KNOWN', name))
            if v % 2 == 1 and lam % 2 == 0 and d * (d - 1) < v - 1: bad.append(('A3_RULE_FIRES', name))
            Z = (A == 0).astype(np.int64)
            ac = np.rint(np.fft.ifftn(np.abs(np.fft.fftn(Z)) ** 2).real).astype(np.int64).reshape(-1)
            if ((ac[1:] - (v + lam)) % 2).any(): bad.append(('A3_PARITY_LEMMA', name))
            st['a3_lemma'] += 1
            if math.gcd(v, n) == 1 and n > 1:
                M = mult_group(n, math.lcm(*shape))
                if len(M) > 1:
                    good, cen = invariant_translate(A, shape, M); st['a5_tests'] += 1
                    if good == 0 or cen is False: bad.append(('A5_THEOREM', name, sorted(M)[:6], good, cen))
            for ds in itertools.product(*[[x for x in range(1, m + 1) if m % x == 0] for m in shape]):
                h = math.prod(ds)
                if h == 1 or math.gcd(h, n) != 1: continue
                M = mult_group(n, math.lcm(*ds))
                if len(M) == 1: continue
                a = np.zeros(ds, dtype=np.int64); I = np.indices(shape).reshape(len(shape), -1)
                np.add.at(a, tuple(I[i] % ds[i] for i in range(len(shape))), A.reshape(-1))
                good, cen = invariant_translate(a, list(ds), M); st['a7_tests'] += 1
                if h == v: st['a7_tests_H=G'] += 1
                if good == 0 or cen is False: bad.append(('A7_THEOREM', name, ds, good, cen))
            print(name, shape, (v, k, lam), flush=True, file=sys.stderr)
    print(dict(st)); print('violations', len(bad))
    for b in bad: print(b)
