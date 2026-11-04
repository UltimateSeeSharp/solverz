# State

**Focus.** The middle of C31 (b)'s ray (catch-up-research's route, in I8's start): Q_N(b) = (I_N ∖ {1, b}, b − 1) no loss for N − 4 > b > 2; endpoints C73, reduction C74, whose open hypotheses are C81 at j = 2 (interior), C82 (({3..N}, 1) draws) and C83 (boundary).
**Next step (no compute).** Desk-check E24 and E25 line by line before the break runs them; then paper work on C85's pre-switch phase (a class of rounds-game states Z can keep, guided by C85 Tried) and on C83 at y = 2 and y = N via C77. Runs wait in the queue below.
**After the queue runs.** I16 (a) survived (E22). I15 (a): E23 at L = 24–26; a non-draw kills C84 as stated. If it survives, I16 (b)/(c), whose answer decides whether PBT has a provable high base. Then C83 for y = N and y = 2 by C77's exact-sum steps (list per N ≤ 28 the defender's safe first turns and whether an exact-sum block from the bottom is always among them). Rule hunting on C81's sets is exhausted (C81 Tried).
- Before offering N = 33–35 to anyone, rerun them from a committed engine with a second engine as a cross-check.
**Limits this session (user, 2026-11-04).** No compute (runs or builds) while the user works; queue each run below, and the user runs the queue on a break.
**Running.**
- Ideator round (model fable, user's request 2026-11-04), told to keep runs tiny and to propose heavier kill tests for the queue below.

## Queued for the user's break
Run from the worktree root (`.worktrees/catch-up`), in order; each line says threads, RAM and time on an idle machine. Builds take seconds: `cargo build --release -p catch-up --bins` (E24 was edited after its last compile check: fix any error first).
- Q1 E23 rest (C84, I15 (a)): `target/release/e23_rank_perturbed.exe 24 26 100 20261105 12 > problems/catch-up/scratch/e23-24-26.txt`: 12 threads, ≤ 4 GB, ~6 min. Any "non-draws" line ≠ 0 kills C84 as stated.
- Q2 E24 (C85, I16 (b), (c)): `target/release/e24_collapsed_rounds.exe 1 10 12 > problems/catch-up/scratch/e24-1-10.txt`: 12 threads, ≤ 3 GB (one HashMap per t), time unknown (p ≤ 8 first: `1 8 12`, seconds to minutes). Decides: Hyb2/Free failing → no first-pick rule works with Hyb2's answers; a rule with 0 failures to p = 10 → (b)'s candidate; TwinHyb2/Max 0 failures in (c)'s family → (c) draws. For p ≤ 7 it also lists the Z starts where max R fails under Hyb2's answers, with the first picks that draw: read them for a rule.
- Q3 E25 (C83): `target/release/e25_boundary_turns.exe 11 24 > problems/catch-up/scratch/e25-11-24.txt`: 1 thread, ≤ 0.2 GB, a few minutes; then `27 28` (1 thread, ~1 GB, maybe 30 min). Shows, per boundary kind of y, whether a safe exact-sum or change turn always exists (C77's route for C83).
- Stopped, rerun when needed: `scratch/a13/lexap.exe 9 9 5 20 > scratch/a13/lexap-9.txt` (C62 progressions, k = 9).

- Q4 (after the download below) port C77, C73, C74 from catch-up-research@b0853b4 into `lean/CatchUp/` (read each file first): `lake build --wfail CatchUp`, a few threads, ~4 GB, minutes per file.

## Needs the user
- Download catch-up-research@b0853b4 (Apache 2.0, GitHub) into `scratch/` to port C77 (exact-sum lemmas), C73 (ray endpoints) and C74 (the lower-ray reduction) into our build; they are Lean-checked there and cited, not yet ours.
- Merge attack/catch-up into main when you want this session's records there (nothing depends on it).
