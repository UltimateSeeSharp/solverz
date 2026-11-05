# State

**Focus.** Three routes end in exact Lean obligations: the band (C86 ⇒ C1, `conjecture_of_band`), C74's ray (`conjecture_of_lower_ray`) and C92's canonical ray (`conjecture_of_canonical_ray`, 2026-11-05: ({3..N}, 1), ({5..N}, 4) and {3..N} minus one adjacent pair at deficit 2 drawing for every even-total N ≥ 13). New and alive (2026-11-05): I23, the low column of blocks (C104, n ≤ 20, E36), and I24, tied one-hole blocks (C105 at every height tested, E34; C106, E35); C1 is an entry of each (C104 through C27; C106 at a = 1, h = top). Their no-loss halves chain: for odd blocks C104's no-loss half follows from C105 and C86 (exact change d when d ≥ a, the minimum pick when d < a; paper, unchecked). The open content of every route is the no-win half, the leader's defense (C31); no simple first pick is always non-losing in C105's no-win positions (the maximum fails in about 4 %, `scratch/a19/mg.rs nw105`).
**Next step.** Ideator round fresh05 is running (Running). Meanwhile: the rounds half of C105 (ROUNDS-B1) as a C23-type theorem, which needs C23's class extended to a tied start with one hole (Z moving with a low hole, Y moving at s = 0); or Lean the chain C105 ∧ C86 ⇒ C104's odd no-loss half. C86 for p = 5 in Lean if the user allows the kernel time (Optional long runs).
**After that.** Return to E24's rule with a new idea (ideator round, or literature on pairing strategies for sum games).
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits (user, 2026-11-04).** Ask before heavy runs while the user works on the machine; light runs (one thread, seconds) are fine.
**Running.**
- Ideator round fresh05 (opus, light runs only), started 2026-11-05 18:00; notes in `scratch/ideator/fresh05/`.

## Optional long runs
- C86 for p = 5 in Lean (draft `scratch/a17/BandFive.lean`, to append to `lean/CatchUp/Band.lean`; kernel evaluation, 1 thread, 2–4 GB; 28 600 distinct positions against 4 265 for p = 4, so about 7× its build time or more if the evaluator does not share subtrees): ask the user first.
- E24 at p = 10 (about 5 h on 6 threads): `target/release/e24_collapsed_rounds.exe 10 10 6`.
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

## Needs the user
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
