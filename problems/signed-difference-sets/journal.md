# Journal

## 2026-11-06
- F4 new (coset sums: absolute sum ≤ k with k's parity; fibre sizes): proved in Lean (`Contraction.lean`), refuter pending
- E7 suspended at 11 of 22 at the user's request: N131 found (O13, Lean pending), N70, N71, N76, N77, N168, N176, N177, N178, N194 exhausted (no Lean proof), N133 cut
- N79, N80: Lean proofs by contraction build (11 of E5's 12); N93 needs the split search (`noVector_of_top`), not yet built; statuses after axioms and the refuter
- Refuter SURVIVES on N35840 (claim and status, `scratch/refuter/n35840-report.md`): proposed as a Solution under "Needs the user"
- E5 (contraction, open v ≤ 40): 12 Instances have no vector on a quotient; Lean's `noVector` proves 9 so far (N46, N47, N95, N168, N176, N220, N221, N223, N224), statuses after axioms and the refuter

## 2026-11-05
- N35840 (361, 316, 141) in C₁₉ × C₁₉: exists, O12 Lean-checked by the new fast set check (`SetCheck.lean`, `decide +kernel`, 77 s); refuter and the literature check next
- E6 (P2, octic cyclotomic sign vectors, every q ≡ 1 mod 8 up to 10⁵): sporadic sets at 9 fields, no family; one open Instance hit, N35840 (361, 316, 141) in C₁₉ × C₁₉: O12, Lean pending
- N67, N73: credited to Gordon 2022 (Prop 2.3, Thm 4.1) by the importer, which now lets a literature construction take the credit over our own set
- Z3 (N49), Z4 (N61), Z5 (N62), Z6 (N68) approved by the user: Solutions in `solutions.md` and the repo README
- Research stopped by the user; E4 stopped at 31 of 53 Instances (`experiments/E4.md`), E5 stopped in its validation with no output
- Refuter on E4's sets: N49, N61, N62, N68 SURVIVE (N61's origin: He–Chen–Ge at m = 1); N67, N73 FLAWED as status: already in Gordon 2022 (Prop 2.3, Thm 4.1), Open in the database by mistake; N63319, N14604, N31832, N14471 lag the same way
- Z1 (N3) and Z2 (N32) approved by the user: Solutions in `solutions.md`
- Goal approved by the user: `IsSDS`, `HasSDS`, and the key → `ZMod` product rule
- Refuter SURVIVES on N3, N32, F2, F3 (independent brute force, Lean rebuild, axioms); F2, F3 verified; N3, N32 proposed as Solutions
- E4 (P1 to the first set, open Instances v ≤ 40): sets O6–O11 settle N49, N61, N62, N67, N68, N73 as exists, Lean-checked (`Answer/N<id>.hasSDS`); none for N30, N89, N90 (no Lean proof yet)
- Migrated to Instances: `instances.csv` from Gordon's table (70,543; He–Wu applied, 22,457 open); S1 → N3, S2 → N32 (`Answer/N3`, `Answer/N32`); `cases.md`, E2 and E3 binaries removed (no runs recorded)
- S1, S2: no SDS, proved in Lean (`CaseS1`, `CaseS2`; F2, F3 in Lean); refuter pending, statuses unchanged until it reports
- Goal audit: refuter SURVIVES on `IsSDS`/`HasSDS`; approval pending
- E1: P1 exhausted for S1 (9,8,1) in C₃×C₃ and S2 (20,17,8) in C₂×C₁₀: no SDS (engine validated, triage script agrees; Lean pending)
- Set up: goal `HasSDS` stated, audit running; O1–O5 checked by `IsSDS` in Lean; F1, F2, P1 new; cases S1, S2 from the triage
