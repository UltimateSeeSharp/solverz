"""feas_enum / feas_dp / feas_milp against plain brute force over multisets, random small inputs."""
import sys, random, itertools
sys.path.insert(0, '.')
from xrules import feas_enum, feas_dp, feas_milp, check_counts
random.seed(7); mism = collections = 0
from collections import Counter
cnt = Counter()
for it in range(1500):
    q = random.choice([2, 3, 4, 5, 7]); c = random.randint(1, 9); h = random.randint(2, 7)
    t = random.randrange(q); V = [x for x in range(-c, c + 1) if (x - t) % q == 0]
    if len(V) < 2: continue
    # sometimes take moments of a random multiset (feasible), sometimes perturb
    ms = [random.choice(V) for _ in range(h)]
    s, Q = sum(ms), sum(x * x for x in ms)
    if random.random() < 0.5: s += random.choice([0, q, -q]); Q += random.choice([0, 2, 4, q * q])
    k = random.randint(0, h * c); 
    bf = any(sum(m) == s and sum(x * x for x in m) == Q for m in itertools.combinations_with_replacement(V, h))
    bfk = any(sum(m) == s and sum(x * x for x in m) == Q and check_counts(V, [m.count(x) for x in V], h, s, Q, k, c)
              for m in itertools.combinations_with_replacement(V, h))
    r = (feas_enum(V, h, s, Q), feas_dp(V, h, s, Q), feas_milp(V, h, s, Q), feas_enum(V, h, s, Q, k, c), feas_milp(V, h, s, Q, k, c))
    exp = (bf, bf, bf, bfk, bfk)
    for name, a, b in zip(['enum', 'dp', 'milp', 'enumA2', 'milpA2'], r, exp):
        cnt[(name, a == b)] += 1
        if a != b and a is not None: print('MISMATCH', name, V, h, s, Q, k, c, a, b)
    cnt['feasible'] += bf; cnt['feasibleA2'] += bfk
print(dict(cnt))
