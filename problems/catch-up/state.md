# State

**Focus.** Five routes now end in exact Lean obligations: the band (C86, `conjecture_of_band`), C74's ray (`conjecture_of_lower_ray`), C92's canonical ray (`conjecture_of_canonical_ray`), and new today the one-hole band (C110, `conjecture_of_one_hole_band`) and the controller games (C112, `conjecture_of_controller_games`, C111 verified). C110 (I24): odd blocks of 2k + 1 minus any one number draw at every deficit d ≤ k − 1 of the parity, at every integer height (k = 3..9, E38; the band ends exactly at d = k); it contains C105, C86 off its diagonal and both of C27's families. Its d = 0 entry is real-height invariant (C109) and proved above the rounds threshold for holes o ≥ k (C108, verified). C112 (I25): neither controller of the tie rule wins on {1..N} at an even total (N ≤ 24, E39), and the controller wins every odd total by exactly 1, a regular sign pattern where the real game's is irregular. C1 and C92 from N = 16 are tie-robust, C86's band is 22 % tie-fragile (ideator data), so a proof of C110 or C86 must use the real tie rule.
**Next step.** Give ideator fresh07's angles (Running) their cheapest kill tests. New today on the low phase: the defender never needs long turns (I27: one number, or the largest number below its deficit and one number, keeps every draw of C1, C110 and C92's families tested, E41, E42), while the attacker's long turns are essential and have no canonical shape; no simple choice of the defender's number works. C108 is verified from linear height (`one_hole_block_draw_linear`); the controller game (I25) is no easier off the root; tied values are not monotone in the height. The leader's defense in the low phase is still the barrier for every route.
**After that.** Return to E24's rule with a new idea (ideator round, or literature on pairing strategies for sum games).
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits (user, 2026-11-04).** Ask before heavy runs while the user works on the machine; light runs (one thread, seconds) are fine.
**Running.**
- Ideator round fresh08 (opus, light runs only), started 2026-11-05 20:27; its notes in `scratch/ideator/`.
- Refuter on today's Lean statements (C110 `OneHoleBandConjecture`, C111 `ctlMargin` vs E39's `Controller`, `OneHoleLinear` wording), started 2026-11-05 20:15; work in `scratch/refuter/`.

## Optional long runs
- C86 for p = 5 in Lean (draft `scratch/a17/BandFive.lean`, to append to `lean/CatchUp/Band.lean`; kernel evaluation, 1 thread, 2–4 GB; 28 600 distinct positions against 4 265 for p = 4, so about 7× its build time or more if the evaluator does not share subtrees): ask the user first.
- E24 at p = 10 (about 5 h on 6 threads): `target/release/e24_collapsed_rounds.exe 10 10 6`.
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

## Needs the user
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
