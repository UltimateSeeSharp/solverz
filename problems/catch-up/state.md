# State

**Focus.** Band-type generalizations of C1 that give an induction slack: I17 (C86 BAND: blocks draw on the whole band d ≤ p at every height; data p ≤ 7), I16 (C85, collapsed blocks; E22 to p = 10), I15 (C84). The route through C31 (b)'s ray (C74's hypotheses C81 at j = 2, C82, C83) stays open; C83 cannot close by C77's recursion alone (C83 Tried).
**Next step (no compute).** Paper: I17's mechanism. Compare the band at heights a and a + 1 on small p by hand from the known rows (C12, C47), and look for why off-diagonal entries are height-invariant (C88): which turn structure changes at a breakpoint, and why it reaches only d = p. Runs wait in the queue below.
**After the queue runs.** Read in order: Q7 (C86, C87: a non-draw off the diagonal kills them as stated), Q9 (C88: interior flips split the descent), Q5 (E26: the same band on collapsed blocks), Q1 (E23, C84), Q2 (E24, I16 (b)/(c)), Q8 (C89), Q3 (E25, C83), Q6 (Lean). A surviving I17 then goes deeper first.
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits this session (user, 2026-11-04).** No compute (runs or builds) while the user works; queue each run below, and the user runs the queue on a break.
**Running.** —

## Queued for the user's break
All at once: `pwsh -File F:\WIN_DATA\Documents\Coding\solverz\.worktrees\catch-up\problems\catch-up\scratch\queue-2026-11-04.ps1` (builds, then everything below in order at BelowNormal priority, outputs in `scratch/`). Or one by one from the worktree root (`.worktrees/catch-up`); each line says threads, RAM and time on an idle machine. Builds take seconds: `cargo build --release -p catch-up --bins` (E24 and E26 were never compiled after their last edit: fix any error first).
- Q1 E23 rest (C84, I15 (a)): `target/release/e23_rank_perturbed.exe 24 26 100 20261105 12 > problems/catch-up/scratch/e23-24-26.txt`: 12 threads, ≤ 4 GB, ~6 min. Any "non-draws" line ≠ 0 kills C84 as stated.
- Q2 E24 (C85, I16 (b), (c)): `target/release/e24_collapsed_rounds.exe 1 8 12`, then `9 10 12` (outputs `scratch/e24-1-8.txt`, `e24-9-10.txt`): 12 threads, ≤ 3 GB (one HashMap per t), seconds to minutes for p ≤ 8, unknown beyond. Decides: Hyb2/Free failing → no first-pick rule works with Hyb2's answers; a rule with 0 failures to p = 10 → (b)'s candidate; TwinHyb2/Max 0 failures in (c)'s family → (c) draws. For p ≤ 7 it also lists the Z starts where max R fails under Hyb2's answers, with the first picks that draw.
- Q3 E25 (C83): `target/release/e25_boundary_turns.exe 11 24 > problems/catch-up/scratch/e25-11-24.txt`: 1 thread, ≤ 0.2 GB, a few minutes; then `27 28` (1 thread, ~1 GB, maybe 30 min).
- Q5 E26 (C85's band, as C86 for blocks): `target/release/e26_collapsed_rows.exe 1 10 6 > problems/catch-up/scratch/e26-1-10.txt`: 6 threads, ≤ 5 GB, ~1 min. Its count of non-draws at d ≤ |t| is the test; non-losses above |t| are expected at low heights (C86's run 4).
- Q6 Lean C33, C38, C37 (3), C7 (`lean/CatchUp/GameMargin.lean`, `Endgames.lean`, written 2026-11-04, never compiled): `lake build --wfail CatchUp.GameMargin CatchUp.Endgames` (a few threads, ~4 GB, minutes); fix errors, `#print axioms` on `valueAux_eq_ofMargin'`, `margin_two_token`, `conjecture_of_margin_le_one`, `valueAux_pair_gap`; then import both in `CatchUp.lean` and mark C33, C38, C7 verified and C37 (3) in Lean.
- Q7 I17 (C86, C87): `scratch/ideator/fresh04/rows.exe 10 24 > scratch/ideator/fresh04/run3-rows-10-24.txt`: 1 thread, ≤ 0.5 GB, 2–5 min (ideator scratch build; a positive result is to be redone with a committed engine).
- Q8 I18 (C89): `scratch/ideator/fresh04/nlb.exe 19 22 5 > scratch/ideator/fresh04/run2-nlb-22.txt`: 1 thread, ≤ 0.2 GB, ~1 min.
- Q9 I17 (C88, BANDSTEP): `scratch/refuter/tir/param.exe p d` for p = 4..6 and every d ≤ p with d ≡ p (mod 2), into `scratch/bandstep-4-6.txt`: 1 thread, minutes per p. Which band entries change value across the height breakpoints.
- Q4 (after the download below) port C77, C73, C74 from catch-up-research@b0853b4 into `lean/CatchUp/` (read each file first): `lake build --wfail CatchUp`, a few threads, ~4 GB, minutes per file.
- After Q6 compiles: C11 in Lean by the plan in C11 (margins; covers a = 1).
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

## Needs the user
- Download catch-up-research@b0853b4 (Apache 2.0, GitHub) into `scratch/` to port C77 (exact-sum lemmas), C73 (ray endpoints) and C74 (the lower-ray reduction) into our build; they are Lean-checked there and cited, not yet ours.
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
