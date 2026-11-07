"""Check Gordon's stored sets (sds.json) for the family's cyclic keys with the own checker."""
import json, sys
from bose import sds_direct, autocorr
d = json.load(open("../../data/gordon/sds.json"))
for key in ["SDS(20,11,2,[20])", "SDS(51,19,3,[51])", "SDS(104,29,4,[104])"]:
    v, k, lam = map(int, key[4:].split(",[")[0].split(","))
    for i, (P, N) in enumerate(d[key]["sets"]):
        D = [0] * v
        for x in P: D[x] += 1
        for x in N: D[x] -= 1
        a = autocorr(D, v)
        print(key, i, "+%d -%d" % (len(P), len(N)), "SDS:", sds_direct(D, v, k, lam),
              "off-peak values:", sorted(set(a[1:])), "N diffs:", sorted({(x - y) % v for x in N for y in N} - {0}))
