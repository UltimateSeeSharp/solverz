# State

**Focus.** Two routes with new footing. I17: the block band C86 holds at integer heights to p = 10 and implies C1 in Lean (`conjecture_of_band`); one-pick-per-turn play reaches it only down to a ≈ 3p/2 (E28), so the open part is the band below that, where multi-pick turns (exact change through whole pairs) carry it. I16: a fixed rounds-game strategy draws every collapsed block (E24, p ≤ 9), a candidate high base for C85. The route through C31 (b)'s ray (C74's hypotheses C81 at j = 2, C82, C83) stays open; C83 holds to N = 28.
**Next step.** Prove E24's rule: in the rounds game on collapsed blocks, Z first picks the top of the highest bumped pair of the current matching and answers by Hyb2. Start from C25's potential (post-switch is proved for multisets, C85 Tried) and E30's shape (Z to move: d ≤ c(R), at most one orphan pair; Y pre-switch: at most two), which needs a restriction on where the orphans sit (({0, 1, 2, 2, 4, 6}, Z at 3) fits the shape and loses): list the orphan placements the rule reaches (extend E30), state the class, then prove it closed round by round as C25 does for Hyb2.
**After that.** C86 at a = 2p − 2: extract E28's drawing strategy at the least height (it exists to p = 8) and look for a rule, as the hand case p = 3 (Hyb2 plus a tie answer, C86 Tried) suggests.
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits (user, 2026-11-04).** Ask before heavy runs while the user works on the machine; light runs (one thread, seconds) are fine.
**Running.** —

## Optional long runs
- E24 at p = 10 (about 5 h on 6 threads): `target/release/e24_collapsed_rounds.exe 10 10 6`.
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

## Needs the user
- Download catch-up-research@b0853b4 (Apache 2.0, GitHub) into `scratch/` to port C77 (exact-sum lemmas), C73 (ray endpoints) and C74 (the lower-ray reduction) into our build; they are Lean-checked there and cited, not yet ours.
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
