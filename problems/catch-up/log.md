# Log

Newest last. Entry format:

### <date>: <title> (<line, or —>)
- **Claim / question.** <precise and falsifiable; for literature, the question>
- **Approach.** <experiment (file, command, runtime, how checked), proof attempt, or search>
- **Outcome.** <holds up to …, the first counterexample, the proof step reached, or what the search found>
- **Refuter.** <verdict and main findings, or "not run (why)">
- **Literature.** <searched what where, found what, or "not searched">
- **Metric.** <line metric before → after>
- **Meaning.** <what it tells us; for failures: why, and how the claim could be weakened>

### 2026-10-22: induction by four fails, even for complete sets (—, conjecture)

- **Claim / question.** If S has even sum and is a draw, adding a balanced quadruple Q = {a < b < c < d}, a + d = b + c, above max(S) keeps it a draw. Q = the next four numbers is the step {1..N} → {1..N+4}, which with N = 0, 3 would prove the conjecture.
- **Approach.** `solver/src/bin/quad_step.rs`: `cargo run --release -p catch-up --bin quad_step -- 30` (2 min, about 4 GB; output in `scratch/quad_step-30.md`). One layered table on {1..U} gives value(S) for every S ⊆ {1..U}: its gap-0 entry, since a gap-0 turn is one pick like the opening. Checked against `Solver` on all subsets of {1..10} and 100 random ones; every reported set re-solved with `Solver` and, up to 9 numbers, with `reference_value`. Identical output with the library at 740f565 and 4b1ce2b.
- **Outcome.** False.
  - Any S: smallest break {2,7,9,14} (draw) + {15,16,17,18} → player-1 win. At U = 30, 32,652 of 32.7M even-sum draws break (0.1%).
  - Complete S (each number ≤ 1 + the sum of the smaller ones, so every amount up to the total can be paid exactly; {1..N} is complete): no break for S ⊆ {1..24}; first break {1,2,4,8,15,17,18,20,25} + {26,27,28,29} → player-1 win (1 of 5.86M complete draws). Non-consecutive quadruples break sooner: {1,2,3,5,6,9,14,18} + {20,22,24,26} → player-1 win.
  - Side result: every complete even-sum S with max ≤ 21 is a draw. Up to max 30, 523 of 93.7M are not, all sparse: first {1,2,3,7,9,11,14,15,22} (player 1 wins by opening 2); all player-1 wins except one loss, {1,2,3,4,6,7,8,16,18,21,22,26,27,29,30}.
- **Refuter.** Not run (failed in testing).
- **Literature.** Web search 2026-10-22: nothing on complete sets or quadruple steps.
- **Metric.** — (no lines yet).
- **Meaning.** Adding four numbers doesn't preserve draws, not even for complete sets, so the interval induction needs more than completeness. The breaks are sparse sets, often starting 1, 2, 4, 8 (guess: few ways to pay each amount; B3). Completeness is also lost after one move (taking 1 breaks it), so the invariant must be about positions (numbers left + gap), not starting sets.

### 2026-10-22: compact GPU tile streaming reaches N = 35 (—)

- **Claim / question.** Can the solver go past N = 32 on this machine, where two whole layers no longer fit in 8 GB of VRAM? And what are the values of {1..N} for N = 33–35?
- **Approach.** New engine `tiled-cuda` (`solver/src/tiled_cuda.rs`, kernel `tiled.cu`). It stores only the gaps a game can reach (gap ≡ amount taken, mod 2), packs 5 cells per byte in base 3 (4 bytes per row up to N = 39 instead of 12), evaluates all cells of a row at once on bit planes, and streams tiles through a VRAM cache (evicting the tile needed farthest ahead), RAM (16 GB) and files on F:. Measured on the way: the per-gap kernel was compute-bound on draw-heavy N (16.8 s of kernels at N = 31; bit planes: 0.93 s); base 3 cost 15% kernel time against 2-bit cells; from N = 34 time goes to disk writes (~100 MB/s sustained), and splitting layers between RAM and file halved N = 34 (209 → 103 s). Checked: tests against `tiled` on every reachable position for N ≤ 12 (in RAM, in files with the smallest VRAM cache, split) and against `layered` on all openings for N ≤ 20 and subsets of {1..8}; two planted kernel bugs caught; N = 1–32 identical to the existing results. Curated run: `catch-up --engine tiled-cuda --top 10 --from 32 35`, 16 min ([results/values-n32-35.md](results/values-n32-35.md)).
- **Outcome.** N = 33: player 1 wins, only by opening 1. N = 34: player 1 wins, only by opening 2. N = 35 (even total): draw, and every opening draws. So the conjecture's prediction holds at N = 35, and the pattern "for even totals every opening draws" continues.
- **Refuter.** Not run (engine work; the N = 33–35 values are unchecked by an independent engine).
- **Literature.** Not searched.
- **Metric.** — (computation reach, not a line metric): exact values N ≤ 32 → N ≤ 35.
- **Meaning.** Even totals up to N = 35 are draws. N = 36 is within reach (estimated 50–60 min, ~170 GB disk writes, ~55 GB peak disk). Odd totals: the winning opening has been a single small number (3, 2, 3, 2, 1, 2 for N = 25, 26, 29, 30, 33, 34), a pattern worth a backlog idea.
