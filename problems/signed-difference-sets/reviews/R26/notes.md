# Refuter notes, I13 (C9/C10 for every n via Witt vectors; Part33-Part59)

Started 2026-11-06. Running notes, newest last.

## Statements read
- MultiplierWitt.lean 527-565: `IsSDS.exists_multiplier'`, `exists_translate_fixed'`, `exists_translate_fixed_contract'`
  differ from Multiplier.lean's C15/C16 by `Squarefree n` -> `n ≠ 0` (to check by diff).
- OrbitSearchWitt.lean: `OrbitRow'` = `OrbitRow` minus the trial-division squarefree conjunct.

## F1 Rows match (check 2) - independent script `reviews/R26/rows.py`
Parsed all 27 parts (1,620 theorems, every one matched the expected 3-line form, none unparsed): group in the
statement = `ms` in the proof = key's factor list; k, λ = key's; status `open`; E10/E11 result `none`; no object
(O1-O70 instance ids, 66); n > 0 not squarefree, gcd(v, n) = 1, gcd(t, v) = 1, t ≡ p^f mod every factor (same f)
for each prime p | n, s² = k + λ(v−1), s ≥ 0. settle-i13.tsv: 1,620 distinct lines, each id in a part, the part
named is the part that holds it, theorem name `SignedDifferenceSets.OrbitRows.n<id>_not_hasSDS`, status `none`.
0 errors. Target recomputed from instances.csv (now) + e10/e11: 1,954 rows (helper W said 1,951; see F2).

## F2 Target count 1,954, not 1,951 (minor, reporting only)
Open + E10/E11 `none` + n not squarefree + gcd(v,n)=1: 1,954 rows (same at cb521cd, ae9f406, 9f618e9). 1,620 in the
parts; the 334 others all have > 1,500 leaves by orbitrows.py's own count (`missing_leaves.py`), so no eligible row
was skipped; helper W's "331 above 1,500 / 1,951 in all" is off by 3. No row claimed wrongly.

## F3 C9 on every known object (check 3) - `known.py`, output `known.out`
Every object file O1-O73 is an SDS (FFT autocorrelation). The 21 with n > 0 and gcd(v,n)=1: a translate fixed by
EVERY t in M = ∩_p <p mod exp G> exists; 14 of them have n not squarefree (O2 n=4, O12 n=175, O24 n=32, O36 n=25,
O37 n=49, O38 n=64, O39 n=49, O58 n=81, O59 n=25, O60 n=49, O63 n=100 (|M|=1), O68 n=81, O69 n=16, O70 n=49).
Control: with all units in place of M no translate is fixed on any of them (the test can fail).
None of the 14 object rows is in a part (F1).

## F4 Axioms and controls in Lean (check 4) - `Axioms.lean`, output `axioms.out` (one lenv-locked run, 38 s)
`#print axioms` on dvd_cross, IsSDS.exists_multiplier', exists_translate_fixed', exists_translate_fixed_contract',
not_hasSDS_of_orbitRow', and part theorems n1157 (Part33, first), n15759 (Part55, C2×C2×C62), n4630 (Part59, last):
only propext, Classical.choice, Quot.sound. Grep of MultiplierWitt, OrbitSearchWitt, Tests/MultiplierWitt, Part33-59:
no sorry, native_decide, axiom, implemented_by, extern, unsafe, opaque, macro/elab, #eval. Oleans newer than sources.
`#check` prints the statements as read (C15/C16's with `Squarefree n` replaced by `n ≠ 0`; Squarefree n ⇒ n ≠ 0, so
strictly stronger). Negative controls by `decide +kernel`, all pass: orbitExhaust = false on known-exists rows with n
not squarefree: [20] (20,11,2) t=3 s=7 (n=9); [23] (23,12,4) t=2 s=10 (n=8); [51] (51,19,3) t=2 s=13 (n=16, O69);
[7] (7,4,0) t=2 s=2 (n=4, O2); and ¬OrbitRow' [51] 19 3 2 13.

## F5 Root does not import the new modules (precondition, not a math error)
`lean/SignedDifferenceSets.lean` imports OrbitRows up to Part32 only; MultiplierWitt, OrbitSearchWitt,
Tests.MultiplierWitt and Part33-Part59 are not imported (helper W's report says so too). CLAUDE.md: `lake build` only
checks what the root imports, and Trust requires `lake build --wfail`. The modules were built one by one with
--wfail (helper's logs) and their oleans load cleanly here, but the 1,620 rows should be recorded as settled only after
the root imports them and the root build passes.

## F6 Literature (check 1, 5) - opened 2026-11-06
- Gordon arXiv:2212.10630 (HTML v1, opened): Thm 5.1, "in McFarland's thesis (see Result 3.2 in [12])": G abelian,
  order v, exponent e; D ∈ Z[G], D D^(−1) ≡ n mod G, gcd(v, n) = 1, n = ∏ p_i^{e_i}; gcd(v, t) = 1 and
  t ≡ p_i^{f_i} mod e for every i ⇒ t is a multiplier and some translate of D is fixed by t. No n > λ, n not
  required squarefree.
- Tan arXiv:1610.01914 (HTML v4, opened): Result 3.2 (McFarland, thesis 1970, Thm 9.1), same hypotheses, D ∈ Z[G],
  "D has a translate D′ = Dg ... such that D′^(t) = D′".
- Lean vs literature: hypotheses identical (t ≡ p^f mod e ⇔ ∀x, t•x = p^f•x; gcd(t, v) = 1; gcd(v, n) = 1; n ≠ 0
  is implicit in n = ∏ p_i^{e_i}). Lean's conclusion is stronger only in one standard way: ONE translate fixed by
  every such t at once (the literature: per t). It rests on gcd(s, v) = 1 (s² = n + μv) and is Lean-proved.
  C10' (integer vector on H, gcd(|H|, n) = 1 only) is Result 3.2 for D ∈ Z[H]; the literature allows it.
- Credit: the theorem is McFarland's (thesis Thm 9.1), as quoted by Tan and Gordon; the Lean proof (Witt vectors in
  place of prime ideals in Z[ζ_v]) is ours. Search "formalized multiplier theorem difference sets Lean OR Isabelle
  OR Coq": no formalization found (result list only, nothing opened).

## F7 Rows' provenance
All 1,620 rows: source `Open@e3bf810` (Gordon's open list), evidence/lean/solution empty; instances.csv keys unique
(no exists row shares a key with a part row).

## F8 Exhaustive small-group test of C9' and of its integer-vector core (C10') - `brute.py`, `brute_int.py`
Every D ∈ {−1,0,1}^G with constant off-zero autocorrelation on C3, C5, C7, C2×C4, C9, C3×C3, C2×C5, C11, C13, C2×C7,
C3×C5 (`brute.out` for orders 10-15): 1,548 sets with n > 0, gcd(v, n) = 1, 736 of them with n not squarefree; every
one has a translate fixed by all of M; 0 failures. Control (all units instead of M, where larger): 592 of 636
not fixed. Integer vectors (C10' core, `exists_translate_fixed_of_autocorr'`), entries in [−3,3] on C3, C5 and in
[−2,2] on C7, C2×C4, C9, C3×C3: 2,906 applicable, 854 with n not squarefree, 0 failures; control 392 of 460 not
fixed. (A first run of brute_int.py with n mis-computed as Σa² reported 1,498 "failures": my bug, fixed; it shows the
test fails when M is wrong.)

## Verdict
SURVIVES (all 27 parts, MultiplierWitt, OrbitSearchWitt); precondition F5 (root imports); F2 bookkeeping.
Report: reviews/R26/report-2026-11-06-2316.md
