"""N32 via C5: integer vectors a on Z5 with sum a^2 = 41 and autocorrelation 32 at every shift != 0.
Unbounded (|a_i| <= 6 follows from sum a^2 = 41), then the [-4,4] box; also near-miss census."""
import itertools
from collections import Counter
sols, near = [], Counter()
for a in itertools.product(range(-6, 7), repeat=5):
    if sum(x * x for x in a) != 41: continue
    c = tuple(sum(a[h] * a[(h + g) % 5] for h in range(5)) for g in range(1, 5))
    if all(x == 32 for x in c): sols.append(a)
    near[c] += 1
print("vectors with sum a^2 = 41:", sum(near.values()))
print("with autocorrelation 32 everywhere:", len(sols), sols[:5])
print("max over vectors of min autocorrelation:", max(min(c) for c in near))
print("sum a values reachable with all corr equal:", sorted({(c[0]) for c in near if len(set(c)) == 1}))
