# Refuter round 4 notes (2026-11-06)

Scope: C23 (CompositeModulus.lean, CompositeModulusRows.lean, 132 rows), I15 objects O40-O60 and
Answer/N<id>.lean, SetCheckSplit.lean, axioms.

## F1 (part 1, C23 rows): the 132 rows recompute exactly — no defect
- `c23_check.py` (own parser, own primality, own self-conjugacy exponent, literal re-implementation of
  `MomentsOk`/`BoxOk`/`CmCert.Kills`; Python `//`,`%` = Lean `Int.ediv`/`emod` for positive divisors):
  132 rows parsed from CompositeModulusRows.lean, 132 distinct ids; each row's (ms, k, λ, v=∏ms) equals
  its instances.csv key; all 132 are `open`; none has an object in objects/_objects.md; every
  certificate satisfies Kills. settle-round4.tsv's 132 `none` ids = the Lean ids, chunk names match.
- Own search over all 70,543 rows (every subset of ≥2 qualifying primes, q ≤ 20,000 vs the solver's
  5,000 and full-set-only): kills 1,181 rows = 132 open + 1,049 already `none`; 0 `exists`.
  Open rows killed = exactly the 132 (none missed, none extra).
- Sanity on known SDSs (`c23_exists.py`): 31 `exists` rows reach the C14/C23 box test (4 with ≥2
  primes); the test kills none of them.
## F2 (part 2, objects and Lean answers): all 22 check — no defect
- `i15_check.py` (own parser, brute-force signed count over every nonzero shift in the header's group,
  own mask decoder using Mathlib's `finProdFinEquiv` order `x.2 + n * x.1`, checked in
  Mathlib/Logic/Equiv/Fin/Basic.lean:330): for O40–O60 and O38 (N58470), the object's group = the row
  key's factors in order, weight = k, every nonzero shift's signed count = λ (single value), header =
  key; the Lean file's `hasSDS` group (`ZMod` factors), `sds` type, k, λ = the key; plus/minus masks
  disjoint, inside `size`, and decode to exactly the object's signed set.
- Split files (N31721, N31722, N32087, N32088, N26075, N47314, N9807, N58470): ranges start at 0, are
  contiguous, end at v; `isSDS` chains `allFrom_append` over shifts2…shiftsN in order; `countOk` uses
  the row's k. (Lean also enforces this: the chained length must be defeq to `Indexed.size G`.)
- Checker validated (`i15_neg.py`): one flipped sign or one dropped element is rejected; O40 read in
  C₁₂₅ instead of C₅ × C₂₅ gives λ ∈ {0,…,6}, rejected.
- Rows: the 19 settle rows are `open`; N1134, N9807 `exists` (Gordon: Orbit Exhaust); N58470 `open`.
## F3 (part 2, literature and credit) — sources opened 2026-11-06
- Gordon, arXiv:2212.10630 (read via ar5iv HTML; arXiv PDF not renderable here): constructions are
  Prop 2.1–2.3, Cor 3.1/Thm 3.2 (4th-power residues), Thm 4.1 (prime pairs) and Table 1 (23 sporadic
  cyclic SDS from a multiplier/orbit search). No relative difference set, no R − N / G − R − 2N /
  G − 2R − N family. Table 1 contains (20,11,2) |P|=9 |N|=2 and (78,53,28) |P|=50 |N|=3: both have
  F4's shape (q = 9, n = 2; q = 25, n = 3), found by computer, not as a family. (104,29,4) |P|=25 |N|=4
  is a C18 point. (200,151,102) is not in Table 1 (N9807's `exists` is Gordon's database).
- He–Chen–Ge, arXiv:2306.05631 (HTML): PDS (Lemma 3.1, Thm 3.7), products (Thm 4.1), cyclotomy
  (Prop 5.3–5.7). No relative difference sets; none of F1/F1′/F3/F4's parameters.
- He–Wu, arXiv:2608.22936 (HTML): Thm 5.3 (PCP-type PDS, (2^{2m}, …), e.g. (64,22,6)), Thm 5.6
  (125,28,3) in C₅³ = (F₂₅,+) × (F₅,+): D = P − N, P = {(x,y) ∈ F₂₅* × F₅*: ρ(x) = σ(y)}, N = {0} × F₅*.
  P ∪ {0} meets every coset of {0} × F₅ once, so this is F1's shape at p = 5 in C₅³ (He–Wu do not
  phrase it via an RDS). C₅ × C₂₅ is not mentioned.
- Gordon, arXiv:2501.14924 (HTML): RDS → circulant weighing matrices (λ = 0) by a sign flip of a
  coset (Thm 12, 13); no λ ≠ 0, no αG + βN + γR.
- Searches: "signed difference set construction from relative difference set semiregular" and
  "relative difference set minus forbidden subgroup … R − N … perfect ternary array" found no SDS
  construction from an RDS; "signed difference sets new construction 2025 OR 2026" found only the
  three SDS papers above.
- Credit per row: N3243 (C₅ × C₂₅), N31721, N31722 (F1); N3314, N3315, N32087, N32088 (F1′);
  N658–N665 (F1, R by DFS); N736–N742 (F1′); N26075 (F3); N47314 (F4): ours (ideator round 2) as SDS
  constructions, citing the classical RDS (semiregular: Pott 1995; affine: Bose 1942). Notes: He–Wu
  have (125,28,3) by the same shape in C₅³ (not a settle row); Gordon's Table 1 has F4's (20,11,2) and
  (78,53,28) as sporadic search results, so F4's family is ours but its small points are Gordon's.
  N1134 and N9807 stay credited to Gordon (`exists` already); O59/O60 are only replacement sets.
## F4 (part 1, wording, minor): C23.md says more than the Lean proves
- claims/C23.md: "C5 (2c < q), C13 and C14 hold with q". Lean (`not_hasSDS_of_compositeModulus`) has
  only C14's box test with q (`BoxOk` = C13's `MomentsOk` ∧ box), so C13-with-q is covered and
  "C5 with q" is not stated. No row needs it: on all 502 quotients (all rows, ≥2 primes) with 2c < q,
  the box test already fails for every t₀ (`c23_c5q.py`). Suggest the claim text say "C14 (with C13)
  holds with q", or add the 2c < q case. Also C23.md's Evidence says 94 rows; the Lean file has 132.
## F5 (part 1, direct test of C23's congruence on real SDSs) — no violation
- `c23_objects.py`: every stored object O1–O60, every quotient H with qualifying primes: the coset sums
  agree mod q = ∏ p^j on all 46 object/quotient pairs (3 with two primes). No stored object or scratch
  `.txt` set has the (v, k, λ) of any of the 132 rows.
- Lean hygiene: CompositeModulus, CompositeModulusRows, SetCheckSplit and all 22 answer modules are
  imported in lean/SignedDifferenceSets.lean; none contains `sorry`, `native_decide`, `axiom`,
  `implemented_by` or `extern`. Commit 655659c changed only `isCoprime_modulusProd`'s proof (no
  statement); the oleans postdate the sources. settle-round4.tsv's object ids and theorem names match
  objects/_objects.md and the answer files.
## F6 (part 3, axioms): clean
- `R4Axioms.lean` via `lenv-locked.sh refuter-r4` (34 s, log `R4Axioms.log`): `#print axioms` gives
  exactly [propext, Classical.choice, Quot.sound] for not_hasSDS_of_compositeModulus,
  CmCert.not_hasSDS, IsSDS.modulusProd_dvd, compositeModulusRows1–4_not_hasSDS and all 22 answers
  (the 19 settle rows, N1134, N9807, N58470). `#check`s show the expected concrete groups and (k, λ);
  two `example`s compile: rows N5513 and N68801 give ¬ HasSDS (ZMod 3 × ZMod 51) 112 12 and
  ¬ HasSDS (ZMod 493) 412 187.
