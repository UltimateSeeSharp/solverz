# State

**Focus.** Five routes now end in exact Lean obligations: the band (C86, `conjecture_of_band`), C74's ray (`conjecture_of_lower_ray`), C92's canonical ray (`conjecture_of_canonical_ray`), and new today the one-hole band (C110, `conjecture_of_one_hole_band`) and the controller games (C112, `conjecture_of_controller_games`, C111 verified). C110 (I24): odd blocks of 2k + 1 minus any one number draw at every deficit d ≤ k − 1 of the parity, at every integer height (k = 3..9, E38; the band ends exactly at d = k); it contains C105, C86 off its diagonal and both of C27's families. Its d = 0 entry is real-height invariant (C109) and proved above the rounds threshold for holes o ≥ k (C108, verified). C112 (I25): neither controller of the tie rule wins on {1..N} at an even total (N ≤ 24, E39), and the controller wins every odd total by exactly 1, a regular sign pattern where the real game's is irregular. C1 and C92 from N = 16 are tie-robust, C86's band is 22 % tie-fragile (ideator data), so a proof of C110 or C86 must use the real tie rule.
**Next step.** I33's kill test (2), the depth measure for C119 (no agents: paused by the user). Then back to the paused line (below). Today's picture of the low phase: the defender never needs long turns (I27; C114, C116 to k ≤ 9), the attacker's long turns are essential and varied, no fixed defender rule works (fresh07, fresh08), and the draw is universal across catch-up-like turn rules (I31). C1 now needs only C119 (one no-win statement per N, `conjecture_of_max_opening`), or any of the family routes.
**Paused (2026-11-05 20:45).** My own line on C110 and I27 at a clean point: C110 holds at every height for k ≤ 9 (E45 + `oneHoleBand_of_bounded_heights`); nothing half done. Taken up now: `T809` as I29.
**Toolbox angles from the user (2026-11-05 20:40), taken up in order.** `T809` mirror (I29): dead, the complement mirror loses {1..N} from N = 4 and the band on high blocks. `T21` Walnut (I30): dead, the rows are period 4 but nothing links the game to an automaton (that link is C1). `T816` temperature (I32): dead as new, cooling is C32's height deformation. `T1011` rule variants (I31, dead): no separating variant within |θ| ≤ 5; θ ≥ 6–7 keeps the high phase but loses the draw (not for lack of small change); the draw at even totals is universal across catch-up-like turn rules (any stopping threshold near the catch-up point, any cap of at least 2 numbers, asymmetric rules), and fails only when a player may take just one number per turn; far variants draw at N = 19, 20 (θ = 6 loses at N = 16 only). Next: I33's depth measure (C119), then back to the paused line.
Already covered (not to redo): `T807` strategy stealing, `T818` far blocks, `T112` decision trees, `T819` tempo, `T334` minimal counterexample.
**After that.** Return to E24's rule with a new idea (ideator round, or literature on pairing strategies for sum games).
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits (user, 2026-11-04).** Ask before heavy runs while the user works on the machine; light runs (one thread, seconds) are fine.
**Agents paused (user, 2026-11-05 20:55).** No ideator, refuter or other agent in this session until the user allows it again (or a new session). Wanted once allowed: a refuter on C116/C114's engine (`ShortTurns`, one implementation) and on I31's universality data; an ideator round after the toolbox angles. Ideator fresh08 handed back (I33, C119; its cuts in `scratch/ideator/2026-11-05-fresh08.md`).
**Running.**
(none)

## Optional long runs
- C114/C116 at C1 roots N = 23, 24 (`ShortTurns`, about 5 GB, 1 thread): ask the user first.
- θ-variants (I31) at N = 23, 24 to see whether θ = 6, 7 draw again at large N (HashMap engine, several GB): ask the user first.
- C86 for p = 5 in Lean (draft `scratch/a17/BandFive.lean`, to append to `lean/CatchUp/Band.lean`; kernel evaluation, 1 thread, 2–4 GB; 28 600 distinct positions against 4 265 for p = 4, so about 7× its build time or more if the evaluator does not share subtrees): ask the user first.
- E24 at p = 10 (about 5 h on 6 threads): `target/release/e24_collapsed_rounds.exe 10 10 6`.
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

## Needs the user
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
