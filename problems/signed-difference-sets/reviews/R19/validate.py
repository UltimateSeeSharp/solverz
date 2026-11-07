# (a) a broken object is caught; (b) kill20 vs explicit multiset enumeration; (c) kill20 vs solver/eisensteinchars.py.
import sys, re, csv, math, itertools, importlib.util
from pathlib import Path
from kill20 import kills, traces
from eis_lib import is_sds, eis_check
from objects20 import load, PF
ms, v, k, lam, D = load(7); x = next(iter(D)); D2 = dict(D); D2[x] = -D2[x]
print("broken O7: sds", is_sds(ms, D2, lam), "viol", len(eis_check(ms, D2, k, lam)[0]))
def kill_brute(N, s, n):
    T = sorted(traces(n)); m = (N - 1) // 2
    return not any((sp + sum(c)) % N == 0 for sp in (s, -s) for c in itertools.combinations_with_replacement(T, m))
spec = importlib.util.spec_from_file_location("gen", PF / "solver/eisensteinchars.py"); gen = importlib.util.module_from_spec(spec); spec.loader.exec_module(gen)
KEY = re.compile(r"SDS\((\d+),(\d+),(-?\d+),\[([\d,]+)\]\)")
trip = set()
for r in csv.DictReader(open(PF / "instances.csv", encoding="utf-8")):
    m = KEY.fullmatch(r["key"]); v, k, lam = map(int, m.groups()[:3]); ms = [int(x) for x in m.group(4).split(",")]
    S = k + lam * (v - 1)
    if S < 0 or math.isqrt(S) ** 2 != S: continue
    c3 = sum(1 for x in ms if x % 3 == 0)
    for a in range(1, min(c3, 4) + 1): trip.add((3 ** a, math.isqrt(S), k - lam))
dis = [t for t in trip if kills(*t) != gen.eis_kills(*t)]
print("triples", len(trip), "kill20 vs generator disagreements", len(dis), dis[:5])
small = [t for t in trip if t[0] == 9]
dis2 = [t for t in small if kills(*t) != kill_brute(*t)]
print("N=9 triples", len(small), "kill20 vs brute multisets disagreements", len(dis2), "kills among them", sum(kills(*t) for t in small))
tr = [n for n in range(0, 3000) if sorted(traces(n)) != sorted(set(gen.eis_traces(n)))]
print("trace sets differ for n in [0,3000):", tr[:10])
