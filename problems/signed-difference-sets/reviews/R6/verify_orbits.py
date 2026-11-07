"""Rebuild the ideator's orbit-sign sets (N352, N286, N638) with my own orbit code and check IsSDS."""
import itertools, sys
sys.path.insert(0, "problems/signed-difference-sets/reviews/R6")
from verify import check, parse_key

def cyc(t, e):
    s, r = {1 % e}, t % e
    while r not in s: s.add(r); r = r * t % e
    return s

CASES = {  # id: (key, multiplier generator t mod exponent e, eps from ideator output)
    "N352": ("SDS(49,33,1,[7,7])", 2, [0, 1, 1, 1, 1, -1, 1, -1, 0, 0, 0, -1, 1, 1, -1, 0, 0]),
    "N286": ("SDS(45,37,1,[3,15])", 2, [1, 1, 0, 1, 0, -1, 1, 1, 1, -1, -1, -1, -1, 1]),
    "N638": ("SDS(63,47,11,[3,21])", 2, [0, 1, 1, 1, -1, 0, 1, 1, 1, 0, 1, 1, 0, -1, -1]),
}
for i, (key, t, eps) in CASES.items():
    v, k, lam, f = parse_key(key)
    e = f[-1]
    M = cyc(t, e)
    seen, orbs = {}, []
    for g in itertools.product(*[range(m) for m in f]):
        if g in seen: continue
        o = {tuple(u * x % m for x, m in zip(g, f)) for u in M}
        for y in o: seen[y] = len(orbs)
        orbs.append(sorted(o))
    assert len(orbs) == len(eps), (i, len(orbs), len(eps))
    ent = [(g, eps[j]) for g, j in seen.items() if eps[j]]
    print(i, "M =", sorted(M), "orbits", len(orbs), check(key, ent))
    print("   plus:", sorted(g for g, s in ent if s == 1))
    print("   minus:", sorted(g for g, s in ent if s == -1))
