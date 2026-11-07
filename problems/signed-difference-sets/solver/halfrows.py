"""Rows killed by C26 at c = 1 through their halved row (`HalfCert.not_hasSDS`), written as Lean.

`halfrows.py [skip.tsv ...]`: for each open row on C_(2^j) x K (one even factor, K the odd part, 2 self-conjugate mod
exp K) with 4 | k - lambda, the halved row (v/2, (k + lambda)/4, lambda/2) on C_(2^(j-1)) x K is looked up in
instances.csv. When it is `none` (or not in the table) with a Lean proof this script can cite or make (a MaRows or MarkedCountsRows entry, an
orbit-search certificate with at most MAX_LEAVES leaves, a C21, C26 or C7 certificate), the row is written with its HalfCert
(the forms A, P onto ZMod (2r) x Grp ks and B, Q from the halved row's group onto ZMod r x Grp ks, each checked here by
the mirrors of MapOk and SurjCert). Rows in the skip files are left out. Writes lean/SignedDifferenceSets/HalfRows.lean
and scratch/c26/half_rows.tsv. Standard library only.
"""
import csv
import itertools
import math
import re
import sys
from pathlib import Path

from marows import KEY, NL, OPEN, conj_exp, crt, lst, map_ok, surj_cert, vp, wrap
import descentrows
import marows
import orbitrows

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / "lean" / "SignedDifferenceSets"
OUT = LEAN / "HalfRows.lean"
MAX_LEAVES = 1500
PER_PART = 6
# rows each built alone: the parts holding them peaked over 14 GB (2026-11-07)
SOLO_ROWS = {"N5436", "N5454", "N5887", "N6055", "N7342", "N7452", "N58699", "N58708", "N58765", "N58804",
             "N58828", "N58834", "N58879", "N60667"}
# rows left out: their halved row's single orbit check needs over 13.6 GB alone (needs OrbitSearchSplit's slices)
DEFER_ROWS = {"N58699", "N58708", "N5887", "N6055", "N60667", "N58828"}
ORBIT_CAP = 2_000_000  # search nodes before an orbit proof is given up
PAIRS = {2 ** a for a in range(8)}
NONE = "none"


def inv_factors(ms):
    """Invariant factors (ascending) of prod Z_m."""
    pp = {}
    for m in ms:
        x, p = m, 2
        while x > 1:
            e = 0
            while x % p == 0:
                x //= p
                e += 1
            if e:
                pp.setdefault(p, []).append(p ** e)
            p += 1
    for p in pp:
        pp[p].sort(reverse=True)
    out = []
    for i in range(max((len(v) for v in pp.values()), default=0)):
        out.append(math.prod(v[i] for v in pp.values() if i < len(v)))
    return sorted(out) or [1]


def forms_onto(src, tgt):
    """Forms (one per target factor) and preimages of the unit vectors for a bijection prod Z_src -> prod Z_tgt, when each
    target factor is a coprime part of one source factor (unit projections, CRT preimages); None otherwise."""
    used = {}
    A, P = [], []
    for t, d in enumerate(tgt):
        cands = [s for s, m in enumerate(src) if m % d == 0 and all(math.gcd(d, e) == 1 for e in used.get(s, []))]
        if not cands:
            return None
        s = cands[0]
        used.setdefault(s, []).append(d)
        A.append([0] * s + [1])
    for t, d in enumerate(tgt):
        s = len(A[t]) - 1
        others = [e for u, e in enumerate(tgt) if u != t and len(A[u]) - 1 == s]
        rest = math.prod(others)
        x = next(y for y in range(src[s]) if y % d == 1 % d and all(y % e == 0 for e in others)) if rest > 1 else 1 % src[s]
        P.append([0] * s + [x])
    if not (map_ok(src, tgt, A) and surj_cert(src, tgt, A, P) and math.prod(src) == math.prod(tgt)):
        return None
    return A, P


def part_entry(prefix, nid):
    """The literal `(⟨id, …⟩, ⟨…⟩)` of row nid in one of the part files, and the part number."""
    for f in sorted(LEAN.glob(f"{prefix}/Part*.lean")):
        text = f.read_text(encoding="utf-8")
        m = re.search(r"\(⟨" + nid[1:] + r", \[[^\]]*\][^⟩]*⟩,\s*⟨.*?⟩\)(?=,\n|\])", text, re.S)
        if m:
            return int(re.search(r"Part(\d+)", f.name).group(1)), " ".join(m.group(0).split())
    return None


def reduced_proof(r2, ms2, k2, lam2):
    """A Lean term for `¬ @HasSDS (Grp ms2) _ inst' k2 lam2`, given `inst'`, or None (r2: its table row or None)."""
    lean = r2["lean"] if r2 else ""
    rid = r2["id"][1:] if r2 else "0"
    if lean.startswith("SignedDifferenceSets.MaRows.not_hasSDS_of_mem_part"):
        e = part_entry("MaRows", r2["id"])
        if e:
            return f"MaRows.not_hasSDS_of_mem_part{e[0]:02d} (x := {e[1]}) (by decide +kernel) inst'"
    if lean.startswith("SignedDifferenceSets.MarkedCountsRows.part"):
        e = part_entry("MarkedCountsRows", r2["id"])
        if e:
            return f"MarkedCountsRows.part{e[0]:02d}_not_hasSDS (x := {e[1]}) (by decide +kernel) inst'"
    v2_, n2 = math.prod(ms2), k2 - lam2
    if n2 > 1 and math.gcd(v2_, n2) == 1:
        s2 = math.isqrt(k2 + lam2 * (v2_ - 1))
        t = orbitrows.generator(ms2, n2)
        sizes = orbitrows.orbit_sizes(ms2, t)
        if (orbitrows.leaves(tuple(sizes), (k2 + s2) // 2, (k2 - s2) // 2) <= MAX_LEAVES
                and orbit_none(ms2, k2, lam2, t, s2)):
            lemma = "not_hasSDS_of_orbitRow" if orbitrows.squarefree(n2) else "not_hasSDS_of_orbitRow'"
            return f"{lemma} (ms := {lst(ms2)}) (t := {t}) (s := {s2}) (by decide +kernel) inst'"
    c = marows.cert(ms2, k2, lam2)
    if c:
        p, r, i, e, b, ks, A, P = c
        cert = f"⟨{p}, {r}, {i}, {e}, {b}, {lst(ks)}, {lst([lst(a) for a in A])}, {lst([lst(q) for q in P])}⟩"
        return (f"MaRowCert.not_hasSDS maRule (w := ⟨{rid}, {lst(ms2)}, {k2}, {lam2}⟩) (c := {cert}) "
                f"(by decide +kernel) (MaRows.cycloFacts_of_mem_maPairs (pr := ({p}, {r})) (by decide)) inst'")
    d = descentrows.cert(ms2, k2, lam2)
    if d:
        r, i, s, ks, A, P = d
        cert = f"⟨{r}, {i}, {s}, {lst(ks)}, {lst([lst(a) for a in A])}, {lst([lst(q) for q in P])}⟩"
        return f"DescentCert.not_hasSDS (w := ⟨{rid}, {lst(ms2)}, {k2}, {lam2}⟩) (c := {cert}) (by decide +kernel) inst'"
    mc = markedcounts().cert(v2_, k2, lam2, ms2)
    if mc:
        p, j, i, ds, s, ws = mc
        wl = ", ".join("⟨" + ", ".join(map(str, w)) + "⟩" for _, w in ws)
        cert = f"⟨⟨{p}, {j}, {i}, {lst(ds)}, {s}⟩, [{wl}]⟩"
        return f"McCert.not_hasSDS (r := ⟨{rid}, {lst(ms2)}, {k2}, {lam2}⟩) (c := {cert}) (by decide +kernel) inst'"
    return None


def orbit_none(ms, k, lam, t, s):
    """The Lean orbit search (mirrored by `orbitsplit.Search`) finds no set: True only when exhausted."""
    from orbitsplit import Search

    class Capped(Search):
        def run(self, node, st):
            if st[0] > ORBIT_CAP:
                raise TimeoutError
            return super().run(node, st)

    S = Capped(ms, k, lam, t, s)
    try:
        return S.run(S.root(), [0, 0, 0])
    except TimeoutError:
        return False


def markedcounts():
    """The C7 generator, imported quietly (it prints on import)."""
    import contextlib
    import io
    with contextlib.redirect_stdout(io.StringIO()):
        import markedcounts as mc
    return mc


def main():
    skip = set()
    for f in sys.argv[1:]:
        skip |= {line.split("\t")[0].strip() for line in open(f, encoding="utf-8") if line.strip()}
    table = list(csv.DictReader(open(ROOT / "instances.csv", encoding="utf-8")))
    bykey = {r["key"]: r for r in table}
    out, tsv = [], []
    for row in table:
        if row["status"] != OPEN or row["id"] in skip or row["id"] in DEFER_ROWS:
            continue
        m = KEY.fullmatch(row["key"])
        v, k, lam = map(int, m.groups()[:3])
        ms = [int(x) for x in m.group(4).split(",")]
        n = k - lam
        even = [t for t, x in enumerate(ms) if x % 2 == 0]
        if n <= 0 or n % 4 or (k + lam) % 4 or lam % 2 or len(even) != 1:
            continue
        s_ix = even[0]
        pj = 2 ** vp(ms[s_ix], 2)
        r = pj // 2
        odd = [x // 2 ** vp(x, 2) for x in ms]
        src = [t for t, x in enumerate(odd) if x > 1]
        ks = [odd[t] for t in src] or [1]
        srcs = src or [s_ix]
        i = conj_exp(2, math.lcm(*ks))
        if i is None or r not in PAIRS:
            continue
        A = [[0] * s_ix + [1]] + [[0] * t + [1] for t in srcs]
        P = [[0] * s_ix + [crt(1, pj, 0, odd[s_ix])]]
        for t, d in zip(srcs, ks):
            P.append([0] * t + [crt(1, d, 0, pj) if t == s_ix else 1 % d])
        if not (map_ok(ms, [2 * r] + ks, A) and surj_cert(ms, [2 * r] + ks, A, P) and v == 2 * r * math.prod(ks)):
            continue
        k2, lam2 = (k + lam) // 4, lam // 2
        ms2 = inv_factors([r] + ks)
        r2 = bykey.get(f"SDS({v // 2},{k2},{lam2},[{','.join(map(str, ms2))}])")
        if r2 and r2["status"] != NONE:
            continue
        fq = forms_onto(ms2, [r] + ks)
        proof = reduced_proof(r2, ms2, k2, lam2)
        if not fq or not proof:
            continue
        B, Q = fq
        cert = (f"⟨{r}, {i}, {lst(ks)}, {lst([lst(a) for a in A])}, {lst([lst(q) for q in P])}, {lst(ms2)}, {k2}, "
                f"{lam2}, {lst([lst(b) for b in B])}, {lst([lst(q) for q in Q])}⟩")
        lam_l = f"({lam})" if lam < 0 else str(lam)
        nid = row["id"]
        about = (f"halved row {r2['id']} {r2['key']}" if r2
                 else f"halved SDS({v // 2},{k2},{lam2},{lst(ms2)}), not in the table,")
        out.append(f"""/-- {nid}: {about} has no SDS. -/
theorem {nid.lower()}_not_hasSDS (inst : Fintype (Grp {lst(ms)})) :
    ¬ @HasSDS (Grp {lst(ms)}) _ inst {k} {lam_l} :=
  have inst' : Fintype (Grp {lst(ms2)}) := Grp.fintype _ (by decide)
  HalfCert.not_hasSDS (w := ⟨{nid[1:]}, {lst(ms)}, {k}, {lam_l}⟩)
    (c := {cert})
    (by decide +kernel) inst'
    ({proof})
    inst
""")
        tsv.append((nid, f"C26 (halved row {r2['id'] if r2 else 'off the table'})"))
    out = [NL.join(wrap(line.strip(), " " * (len(line) - len(line.lstrip()))) if len(line) > 100 else line
                   for line in block.split(NL)) for block in out]
    (OUT.parent / "HalfRows").mkdir(exist_ok=True)
    ids = [nid for nid, _ in tsv]
    regular = [b for nid, b in zip(ids, out) if nid not in SOLO_ROWS]
    solo = [(nid, b) for nid, b in zip(ids, out) if nid in SOLO_ROWS]
    parts = [regular[i: i + PER_PART] for i in range(0, len(regular), PER_PART)]
    where = {nid: f"HalfRows Solo {nid}" for nid, _ in solo}
    for num, part in enumerate(parts, 1):
        for b in part:
            where[re.search(r"theorem (n\d+)_not_hasSDS", b).group(1).upper()] = f"HalfRows Part{num:02d}"
    tsv = [f"{nid}\tnone\t{why}; {where[nid]}\tSignedDifferenceSets.HalfRows.{nid.lower()}_not_hasSDS" for nid, why in tsv]
    def write_rows(path, title, rows):
        path.write_text(f"""module

public import SignedDifferenceSets.MaDescentFull
public import SignedDifferenceSets.MaRows.All
public import SignedDifferenceSets.MarkedCountsRows.Part01
public import SignedDifferenceSets.OrbitSearchWitt

/-!
# Rows killed by C26 at `c = 1` through their halved row, {title}

{len(rows)} open rows on `C_(2^j) × K` whose halved row `(v/2, (k + λ)/4, λ/2)` has no SDS
by a Lean proof cited or made here (`HalfCert.not_hasSDS`); generated by `solver/halfrows.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.HalfRows

set_option maxRecDepth 100000
-- one kernel check at a time: parts of 15 rows peaked at 7–14 GB in parallel
set_option Elab.async false

{NL.join(rows)}
end SignedDifferenceSets.HalfRows
""", encoding="utf-8", newline=NL)

    for num, part in enumerate(parts, 1):
        write_rows(OUT.parent / "HalfRows" / f"Part{num:02d}.lean", f"part {num:02d}", part)
    (OUT.parent / "HalfRows" / "Solo").mkdir(exist_ok=True)
    for nid, b in solo:
        write_rows(OUT.parent / "HalfRows" / "Solo" / f"{nid}.lean", f"{nid} alone", [b])
    imports = "".join(f"public import SignedDifferenceSets.HalfRows.Part{num:02d}\n" for num in range(1, len(parts) + 1))
    imports += "".join(f"public import SignedDifferenceSets.HalfRows.Solo.{nid}\n" for nid, _ in solo)
    OUT.write_text(f"""module

{imports}
/-!
# Rows killed by C26 at `c = 1` through their halved row

{len(out)} rows: {len(regular)} in {len(parts)} parts (`HalfRows/PartNN.lean`), {len(solo)} built alone
(`HalfRows/Solo/`, too big beside others); generated by `solver/halfrows.py`.
-/
""", encoding="utf-8", newline="\n")
    (ROOT / "scratch" / "c26" / "half_rows.tsv").write_text("\n".join(tsv) + "\n", encoding="utf-8", newline="\n")
    print(len(out), "rows")


if __name__ == "__main__":
    main()
