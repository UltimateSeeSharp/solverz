# State

**Focus.** Two routes with new footing. I17: the block band C86 holds at integer heights to p = 10 and implies C1 in Lean (`conjecture_of_band`); one-pick-per-turn play reaches it only down to a ≈ 3p/2 (E28), so the open part is the band below that, where multi-pick turns of no simple shape carry it (C86 Tried). I16: a fixed rounds-game strategy draws every collapsed block (E24, p ≤ 9), a candidate high base for C85. The route through C31 (b)'s ray (C74's hypotheses C81 at j = 2, C82, C83) stays open; C83 holds to N = 28.
**Next step.** C86 below 2p − 1 by a potential per height: E24's rule's proof is parked (C85 Tried: static, shape and maintained-matching classes all admit losing members). Take C25's W with the height a in it (W_a ≤ a at every round start, so the cap holds) and search, on blocks p ≤ 6 at a = E28's least height, for a Z strategy (multi-pick turns allowed) that keeps a candidate W_a non-increasing; start from the drawing answers E31 extracted (`scratch/e31-breaks-5.txt`).
**After that.** Return to E24's rule with a new idea (ideator round, or literature on pairing strategies for sum games).
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits (user, 2026-11-04).** Ask before heavy runs while the user works on the machine; light runs (one thread, seconds) are fine.
**Running.** — (ideator round fresh04b stopped by the user before writing notes)

## Optional long runs
- E24 at p = 10 (about 5 h on 6 threads): `target/release/e24_collapsed_rounds.exe 10 10 6`.
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

## Needs the user
- Download catch-up-research@b0853b4 (Apache 2.0, GitHub) into `scratch/` to port C77 (exact-sum lemmas), C73 (ray endpoints) and C74 (the lower-ray reduction) into our build; they are Lean-checked there and cited, not yet ours.
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
