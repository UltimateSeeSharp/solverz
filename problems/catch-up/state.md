# State

**Focus.** Five routes now end in exact Lean obligations: the band (C86, `conjecture_of_band`), C74's ray (`conjecture_of_lower_ray`), C92's canonical ray (`conjecture_of_canonical_ray`), and new today the one-hole band (C110, `conjecture_of_one_hole_band`) and the controller games (C112, `conjecture_of_controller_games`, C111 verified). C110 (I24): odd blocks of 2k + 1 minus any one number draw at every deficit d ≤ k − 1 of the parity, at every integer height (k = 3..9, E38; the band ends exactly at d = k); it contains C105, C86 off its diagonal and both of C27's families. Its d = 0 entry is real-height invariant (C109) and proved above the rounds threshold for holes o ≥ k (C108, verified). C112 (I25): neither controller of the tie rule wins on {1..N} at an even total (N ≤ 24, E39), and the controller wins every odd total by exactly 1, a regular sign pattern where the real game's is irregular. C1 and C92 from N = 16 are tie-robust, C86's band is 22 % tie-fragile (ideator data), so a proof of C110 or C86 must use the real tie rule.
**Next step.** Give ideator fresh08's angles (Running) their cheapest kill tests. Today's state of the low phase: the defender never needs long turns (I27, C114, C116 to k ≤ 9, E41, E42, E44), the attacker's long turns are essential and varied, and no fixed defender rule works (fresh07: tie hand-over rules, balance seeking, C116-shaped choices). C110 holds at every height for k ≤ 9 (E38 with the refuter's gap run); its draw region is widest at low heights and tightest in the rounds regime, where Lean has it from linear height for part of the band; a rounds-structure strategy reaches down to about 3k/2 + 1. The leader's defense below that is still the barrier for every route.
**Paused (2026-11-05 20:45).** My own line on C110 and I27 at a clean point: C110 holds at every height for k ≤ 9 (E45 + `oneHoleBand_of_bounded_heights`); nothing half done. Taken up now: `T809` as I29.
**Toolbox angles from the user (2026-11-05 20:40), taken up in order.** `T809` mirror (I29): dead, the complement mirror loses {1..N} from N = 4 and the band on high blocks. `T21` Walnut (I30): dead, the rows are period 4 but nothing links the game to an automaton (that link is C1). `T816` temperature (I32): dead as new, cooling is C32's height deformation. `T1011` rule variants (I31): no separating variant; the draw at even totals is universal across catch-up-like turn rules (any stopping threshold near the catch-up point, any cap of at least 2 numbers, asymmetric rules), and fails only when a player may take just one number per turn; far variants (θ = 4, 5, 6, −4; L = 2) at N = 16, 19, 20 running (`scratch/a19/variant/far.txt`).
Already covered (not to redo): `T807` strategy stealing, `T818` far blocks, `T112` decision trees, `T819` tempo, `T334` minimal counterexample.
**After that.** Return to E24's rule with a new idea (ideator round, or literature on pairing strategies for sum games).
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits (user, 2026-11-04).** Ask before heavy runs while the user works on the machine; light runs (one thread, seconds) are fine.
**Running.**
- Ideator round fresh08 (opus, light runs only), started 2026-11-05 20:27; its notes in `scratch/ideator/`.

## Optional long runs
- C86 for p = 5 in Lean (draft `scratch/a17/BandFive.lean`, to append to `lean/CatchUp/Band.lean`; kernel evaluation, 1 thread, 2–4 GB; 28 600 distinct positions against 4 265 for p = 4, so about 7× its build time or more if the evaluator does not share subtrees): ask the user first.
- E24 at p = 10 (about 5 h on 6 threads): `target/release/e24_collapsed_rounds.exe 10 10 6`.
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

## Needs the user
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
