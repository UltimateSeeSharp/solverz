# State

**Focus.** Two routes with new footing. I17: the block band C86 holds at integer heights to p = 10 and implies C1 in Lean (`conjecture_of_band`); one-pick-per-turn play reaches it only down to a ≈ 3p/2 (E28), so the open part is the band below that, where multi-pick turns of no simple shape carry it (C86 Tried). I16: a fixed rounds-game strategy draws every collapsed block (E24, p ≤ 9), a candidate high base for C85. The route through C31 (b)'s ray (C74's hypotheses C81 at j = 2, C82, C83) stays open; C83 holds to N = 28. In Lean the ray now gives C1 once those three hold for every even-total N ≥ 13 (`conjecture_of_lower_ray`, 2026-11-05), so both routes end in exact Lean obligations. The ray has two simpler verified forms (C91 successor, C92 canonical), whose one-parameter hypotheses hold at every even-total N from 11 to 28 (E33); C92 needs only draws: ({3..N}, 1), ({5..N}, 4) and {3..N} minus one adjacent pair at 2. catch-up-research's written routes are migrated (C90–C103, I20–I22, 2026-11-05).
**Next step.** Both proof searches are parked for now (C85 Tried: no sufficient class for E24's rule; C86 Tried: the least capped height depends on more of R than C25's features). An ideator round is running (Running); meanwhile weigh C92 as the ray's target (assemble it in Lean like `conjecture_of_lower_ray`; compare its draw families with C81's two-sided draw data), or extend `band_draw_le_four` to p = 5 if the user allows a few minutes of kernel time. C83's partial case (y = N, b = N − 1) is already verified (`interval_tail_value_ne_loss_of_deficit_eq_top_add_three`).
**After that.** Return to E24's rule with a new idea (ideator round, or literature on pairing strategies for sum games).
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits (user, 2026-11-04).** Ask before heavy runs while the user works on the machine; light runs (one thread, seconds) are fine.
**Running.**
- Ideator round fresh04c (model fable, light runs only), started 2026-11-04; notes in `scratch/ideator/fresh04c/`.

## Optional long runs
- C86 for p = 5 in Lean (draft `scratch/a17/BandFive.lean`, to append to `lean/CatchUp/Band.lean`; kernel evaluation, 1 thread, 2–4 GB; 28 600 distinct positions against 4 265 for p = 4, so about 7× its build time or more if the evaluator does not share subtrees): ask the user first.
- E24 at p = 10 (about 5 h on 6 threads): `target/release/e24_collapsed_rounds.exe 10 10 6`.
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

## Needs the user
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
