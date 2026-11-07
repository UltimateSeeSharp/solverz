"""Can P' = U_{x in C2^2} P_x x {x} be NL_{2n}(r') in G x C2^2, each P_x built from ONE NL_n(r) set P of G
(blocks: {}, {0}, P, P+0, Pc, Pc+0, G, G-0; Pc = G-0-P)? Character values by the dual indicator e."""
import itertools
def blocks(n, r, k):
    v = n * n
    # name: (size, value for nontrivial chi with dual indicator e)
    return {"0": (0, lambda e: 0), "{0}": (1, lambda e: 1), "P": (k, lambda e: r - n * e), "P+0": (k + 1, lambda e: r + 1 - n * e),
            "Pc": (v - 1 - k, lambda e: -1 - r + n * e), "Pc+0": (v - k, lambda e: -r + n * e), "G": (v, lambda e: 0), "G-0": (v - 1, lambda e: -1)}
PSI = [(1, 1, 1, 1), (1, 1, -1, -1), (1, -1, 1, -1), (1, -1, -1, 1)]  # values on 0,a,b,c
found = {}
for n in (4, 8, 16, 32):
    for r in range(1, n - 1):
        k = r * (n + 1)
        B = blocks(n, r, k)
        for combo in itertools.product(B, repeat=4):
            if combo[0] in ("{0}", "P+0", "Pc+0", "G"): continue  # 0 of G' not in P'
            size = sum(B[c][0] for c in combo)
            N2 = 2 * n
            if size == 0 or size % (N2 + 1): continue
            rp = size // (N2 + 1)
            if not (0 < rp < N2 - 1): continue
            ok = True
            for psi in PSI:
                for chi in ("triv", 0, 1):
                    if chi == "triv" and psi == PSI[0]: continue
                    val = sum(p * (B[c][0] if chi == "triv" else B[c][1](chi)) for p, c in zip(psi, combo))
                    if val not in (rp, rp - N2): ok = False
            if ok:
                found.setdefault((n, r), set()).add((rp, combo))
for (n, r), s in sorted(found.items()):
    rps = sorted({x[0] for x in s})
    print(f"NL_{n}({r}) -> NL_{2*n}(r') for r' in {rps}; e.g.", [x for x in s if x[0] == rps[0]][0][1])
