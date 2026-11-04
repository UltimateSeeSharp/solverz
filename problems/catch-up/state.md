# State

**Focus.** Two routes with new footing. I17: the block band C86 holds at integer heights to p = 10 and implies C1 in Lean (`conjecture_of_band`); one-pick-per-turn play reaches it only down to a ≈ 3p/2 (E28), so the open part is the band below that, where multi-pick turns of no simple shape carry it (C86 Tried). I16: a fixed rounds-game strategy draws every collapsed block (E24, p ≤ 9), a candidate high base for C85. The route through C31 (b)'s ray (C74's hypotheses C81 at j = 2, C82, C83) stays open; C83 holds to N = 28.
**Next step.** Both proof searches are parked for now (C85 Tried: no sufficient class for E24's rule; C86 Tried: the least capped height depends on more of R than C25's features). An ideator round is running (Running); meanwhile port what needs no download: state C83's partial case (y = N, b = N − 1) in Lean once C77 is ours, or extend `band_draw_le_four` to p = 5 if the user allows a few minutes of kernel time.
**After that.** Return to E24's rule with a new idea (ideator round, or literature on pairing strategies for sum games).
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits (user, 2026-11-04).** Ask before heavy runs while the user works on the machine; light runs (one thread, seconds) are fine.
**Running.**
- Ideator round fresh04c (model fable, light runs only), started 2026-11-04; notes in `scratch/ideator/fresh04c/`.

## Optional long runs
- E24 at p = 10 (about 5 h on 6 threads): `target/release/e24_collapsed_rounds.exe 10 10 6`.
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

## Needs the user
- Download catch-up-research@b0853b4 (Apache 2.0, GitHub) into `scratch/` to port C77 (exact-sum lemmas), C73 (ray endpoints) and C74 (the lower-ray reduction) into our build; they are Lean-checked there and cited, not yet ours.
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
