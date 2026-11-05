# State

**Focus.** Session plan of 2026-11-05 (user), stepped with the user: each step reported, the next only on the user's go, until the user says "go loop".
1. P2: cyclotomic classes of order 8 in GF(q), q ≡ 1 mod 8 (N49's O6 is one, `scratch/refuter/r4-report.md`); every sign (+, −, unmarked) on the classes, 0 marked or not. Which give SDSs, and for which open Instances? A family would be a paper. Minutes of compute.
2. A Lean non-existence checker: first contraction (F3: no integer vector on a quotient meets the conditions; a verified search the kernel evaluates), tested on N32 and the E4 Instances contraction kills; then exhaustion for cases like N3. The design goes to the user before any code: what it proves, how Lean evaluates it, expected speed.
3. Background meanwhile: E4's 9 unchecked sets (N127–N130, N132, N137, N139, N169, N170) as objects, Lean-checked, each checked against Gordon, He–Chen–Ge and He–Wu before it is proposed; E4's 22 unreached Instances with v ≤ 40 finished.
4. Once the checker settles its first cases, the user and the researcher pick the range: open entries with v < 50, v < 100, or more.
**Next step.** Step 1 (P2).
**Running.** nothing.

## Needs the user
- Findings to bring to the user: N63319, N14604, N31832, N14471 are settled in Gordon or He–Chen–Ge, so `instances.csv` lists them as open wrongly.
- Uncommitted in the worktree since the last session: the contraction engine for E5 (`solver/src/contraction.rs`, `instances.rs`, `bin/r5_contraction.rs`, two `mod` lines in `lib.rs`); its first run stopped in validation with no output, so it is unchecked; its doc comment still says R5. Taken up in step 2.
