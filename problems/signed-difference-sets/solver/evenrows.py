"""Rows killed by C28 (the even contraction), written as Lean: `lean/SignedDifferenceSets/EvenRows.lean`.

`evenrows.py <explorer output> <ids file> <max nodes>`: for each row of the ids file with a `KILL [lf]:c<c>:<nodes>` line
from `x_even_contraction` (L = lf = [2^(j-1)] + ds) and at most max nodes, builds the `EvenCert` (the map onto
ZMod (2r) x Grp ks as in `descentrows.py`, K the largest bound <= k/2 with K = s/2 mod 2) and the search proof: one
`decide +kernel` when the search has at most BRANCH_NODES nodes, else split by `noVector_of_top` into checks of at most
BRANCH_NODES nodes (`answer.prefix_nodes`). Writes `scratch/c26/even_rows.tsv`. Standard library only.
"""
import math
import re
import sys
from pathlib import Path

from answer import BRANCH_NODES, prefix_nodes
from marows import KEY, conj_exp, crt, lst, map_ok, surj_cert, vp

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "lean" / "SignedDifferenceSets" / "EvenRows.lean"
TSV = ROOT / "scratch" / "c26" / "even_rows.tsv"
PAIRS = {2 ** a for a in range(8)}
LINE = re.compile(r"(N\d+) (\S+) KILL \[([\d, ]*)\]:c(\d+):(\d+)")
NL = "\n"


def cert(ms, k, lam, lf, c):
    """(r, i, s, K, ks, A, P) for the quotient the explorer killed on, or None."""
    v = math.prod(ms)
    s = math.isqrt(k + lam * (v - 1))
    odd = [m // 2 ** vp(m, 2) for m in ms]
    for s_ix, m in enumerate(ms):
        for j in range(1, vp(m, 2) + 1):
            r = 2 ** (j - 1)
            ds = lf[1:] if r > 1 else lf
            if (r > 1 and lf[0] != r) or v != 2 * r * math.prod(ds) * c:
                continue
            # place each d of ds in an odd part it divides (one d per factor, as descentrows does)
            dl, used = [1] * len(ms), set()
            for d in ds:
                t = next((t for t in range(len(ms)) if t not in used and odd[t] % d == 0), None)
                if t is None:
                    break
                dl[t] = d
                used.add(t)
            else:
                i = conj_exp(2, math.lcm(*dl))
                src = [t for t, d in enumerate(dl) if d > 1]
                ks = [dl[t] for t in src] or [1]
                srcs = src or [s_ix]
                A = [[0] * s_ix + [1]] + [[0] * t + [1] for t in srcs]
                P = [[0] * s_ix + [crt(1, 2 * r, 0, dl[s_ix])]]
                for t, d in zip(srcs, ks):
                    P.append([0] * t + [crt(1, d, 0, 2 * r) if t == s_ix else 1 % d])
                if i is None or r not in PAIRS or not (map_ok(ms, [2 * r] + ks, A) and surj_cert(ms, [2 * r] + ks, A, P)):
                    continue
                half_k = k // 2
                K = half_k if (half_k - s // 2) % 2 == 0 else half_k - 1
                ok = ((k - lam) % 4 == 0 and s % 2 == 0 and (k + lam * (2 * c - 1)) % 4 == 0 and (lam * c) % 2 == 0
                      and k < 2 * K + 4)
                if ok:
                    return r, i, s, K, ks, A, P
    return None


def main():
    lines = {m.group(1): m for m in map(LINE.match, open(sys.argv[1], encoding="utf-8")) if m}
    ids = [l.split()[0] for l in open(sys.argv[2], encoding="utf-8") if l.strip()]
    cap = int(sys.argv[3])
    blocks, tsv = [], []
    for nid in ids:
        m = lines.get(nid)
        if not m or int(m.group(5)) > cap:
            continue
        v, k, lam, msx = KEY.fullmatch(m.group(2)).groups()
        v, k, lam, ms = int(v), int(k), int(lam), [int(x) for x in msx.split(",")]
        lf, c = [int(x) for x in m.group(3).replace(" ", "").split(",")], int(m.group(4))
        ce = cert(ms, k, lam, lf, c)
        assert ce, nid
        r, i, s, K, ks, A, P = ce
        n = r * math.prod(ks)
        Q, t, s2 = (k + lam * (2 * c - 1)) // 4, lam * c // 2, s // 2
        low = nid.lower()
        lam_l = f"({lam})" if lam < 0 else str(lam)
        head = f"""/-- {nid} {m.group(2)}: `L = ZMod {r} × Grp {lst(ks)}`, `c = {c}`, `Q = {Q}`,
`t = {t}`, `K = {K}`, `Σ Z = ±{s2}` ({m.group(5)} search nodes). -/
def {low}Row : Row := ⟨{nid[1:]}, {lst(ms)}, {k}, {lam_l}⟩

/-- {nid}'s certificate. -/
def {low}Cert : EvenCert :=
  ⟨{r}, {i}, {s}, {K}, {lst(ks)}, {lst([lst(a) for a in A])}, {lst([lst(q) for q in P])}⟩

theorem {low}_ok : {low}Cert.Ok {low}Row := by decide +kernel
"""
        total = sum(prefix_nodes(n, c, Q, s2, 1).values()) + 1
        if total <= BRANCH_NODES:
            search = f"""set_option maxRecDepth 100000 in
theorem {low}_search : {low}Cert.search {low}Row = true := by decide +kernel
"""
        else:
            depth = next(d for d in range(2, n + 1) if max(prefix_nodes(n, c, Q, s2, d).values()) <= BRANCH_NODES)
            counts = prefix_nodes(n, c, Q, s2, depth)
            batches, cur, size = [], [], 0
            for pre, cnt in counts.items():
                if cur and size + cnt > BRANCH_NODES:
                    batches.append(cur)
                    cur, size = [], 0
                cur.append(pre)
                size += cnt
            batches.append(cur)
            NL2 = NL + NL
            defs = NL2.join(
                f"/-- Prefixes, batch {q}. -/{NL}def {low}Batch{q} : List (List ℤ) :={NL}  ["
                + ("," + NL + "    ").join("[" + ", ".join(map(str, pre)) + "]" for pre in bt) + "]" + NL2
                + f"set_option maxRecDepth 100000 in{NL}theorem {low}_below{q} :"
                + f" ∀ p ∈ {low}Batch{q}, {low}Check p = true := by{NL}  decide +kernel"
                for q, bt in enumerate(batches))
            plist, pline = [], ""
            for q in range(len(batches)):
                piece = f"{low}Batch{q}" + (" ++ " if q < len(batches) - 1 else "")
                if len(pline) + len(piece) > 94:
                    plist.append(pline.rstrip())
                    pline = ""
                pline += piece
            plist = (NL + "    ").join(plist + [pline])
            alts = " | ".join("h" for _ in batches)
            assoc = ", or_assoc" if len(batches) > 2 else ""
            names = [f"{low}_below{q} p h" for q in range(len(batches))]
            exacts, line = [], "      exacts ["
            for q, nm in enumerate(names):
                piece = nm + (", " if q < len(names) - 1 else "])")
                if len(line) + len(piece) > 98:
                    exacts.append(line.rstrip())
                    line = "        "
                line += piece
            exacts.append(line)
            search = f"""theorem {low}_pos : ∀ d ∈ {low}Cert.r :: {low}Cert.ks, 0 < d := by decide

/-- `below` with {nid}'s search arguments. -/
abbrev {low}Check (p : List ℤ) : Bool :=
  below (@Indexed.size (Grp ({low}Cert.r :: {low}Cert.ks)) _ (Grp.indexed _ {low}_pos))
    (@Indexed.addIdx (Grp ({low}Cert.r :: {low}Cert.ks)) _ (Grp.indexed _ {low}_pos))
    ({low}Cert.c {low}Row)
    (({low}Row.k + {low}Row.lam * (2 * ({low}Cert.c {low}Row : ℤ) - 1)) / 4)
    ({low}Row.lam * {low}Cert.c {low}Row / 2) {low}Cert.K ({low}Cert.s / 2)

{defs}

/-- The prefixes of {depth} coordinates ({total} nodes in {len(batches)} batches of at most
{BRANCH_NODES}). -/
def {low}Prefixes : List (List ℤ) :=
  {plist}

theorem {low}_search : {low}Cert.search {low}Row = true :=
  onGrp_of {low}_pos (noVector_of_top (P := {low}Prefixes) (d := {depth - 1}) (by decide)
    (by decide +kernel) fun p hp => by
      simp only [{low}Prefixes, List.mem_append{assoc}] at hp
      rcases hp with {alts}
""" + NL.join(exacts) + NL
        blocks.append(head + "\n" + search + f"""
/-- {nid} has no SDS (C28). -/
theorem {low}_not_hasSDS (inst : Fintype (Grp {lst(ms)})) :
    ¬ @HasSDS (Grp {lst(ms)}) _ inst {k} {lam_l} :=
  EvenCert.not_hasSDS (w := {low}Row) (e := {low}Cert) {low}_ok {low}_search inst
""")
        tsv.append(f"{nid}\tnone\tC28; EvenRows\tSignedDifferenceSets.EvenRows.{low}_not_hasSDS")
    OUT.write_text(f"""module

public import SignedDifferenceSets.EvenContraction

/-!
# Rows killed by C28 (the even contraction)

{len(blocks)} open rows, each with an `EvenCert` (`EvenCert.Ok` by `decide +kernel`) and its search on
`ZMod r × Grp ks`, split into checks of at most {BRANCH_NODES} nodes where larger; generated by
`solver/evenrows.py` from `x_even_contraction`'s kills.
-/

@[expose] public section

namespace SignedDifferenceSets.EvenRows

-- one kernel check at a time: each search batch holds up to ~2 GB
set_option Elab.async false

{chr(10).join(blocks)}
end SignedDifferenceSets.EvenRows
""", encoding="utf-8", newline="\n")
    TSV.write_text("".join(x + "\n" for x in tsv), encoding="utf-8", newline="\n")
    print(len(blocks), "rows")


if __name__ == "__main__":
    main()
