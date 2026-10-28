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

### 2026-10-22: a top pair does not act locally; top twins cancel (A1)

- **Claim / question.** B1. V(R, g) = mover's value with R left, trailing by g. (1) Twins: V(S ⊎ {x, x}, g) = V(S, g) for x ≥ max(S), g ≤ x (multisets). (2) Pair rule: V(R ∪ {x, x+1}, g) is a function of V(R, g−1), V(R, g), V(R, g+1) for x > max(R).
- **Approach.** `solver/src/bin/pair_step.rs`: `cargo run --release -p catch-up --bin pair_step -- 22` (51 s; output `scratch/pair_step-22.md`). Twins with `Solver` on every S ⊆ {1..12}, x − max(S) ∈ {0, 1, 3}, values cross-checked with `reference_value` up to 7 numbers. Pairs from one layered table on {1..22} (checked against `Solver` on 20,000 random positions; every printed example re-solved on its own numbers), sliced by g ≤ max(R), max(R) < g ≤ x, g > x and by x = max(R) + 1 or not; then windows V(R, g−w..g+w), w ≤ 4, over all R and over intervals alone.
- **Outcome.**
  - Twins: 163,846 positions, none differ. Reason (mirror): every deficit stays ≤ x, so taking x ends the turn at once and the reply x returns the opponent to the same deficit with the same S; if S runs out first, the two x's go one each and the final difference is unchanged. Both conditions are needed: g > x or x < max(S) give differences (refuter).
  - Pair rule false in every slice. Smallest: R = {} and R = {1..7} both have V(R, 0..1) = D, L, yet V({1,2}, 0) = W and V({1..9}, 0) = L. Wider windows don't help: w = 4 leaves 1,601 of 1,931 keys undetermined over all R; adding x, g, x − max(R) and sum(R) mod 2 to the key still leaves 105,522 of 298,272 (refuter). Same x: R = {1,2,3,5} and {2,4,5}, x = 6, g = 1, same V(R, 0..2) = W, D, L, give L and W.
  - Interval rows V({1..m}, g), m ≤ 21, printed for g ≤ 22: from m ≈ 14 they follow the parity rule except at g ≤ 1.
- **Refuter.** SURVIVES. Independent DP over {1..22} without the crate reproduces every count; twins also hold for all S ⊆ {1..12}, x ≤ 30, and on small multisets. Found a mislabelled column (interval conflicts counted positions, not keys; fixed) and a latent `Solver::position` hazard: a gap above max(numbers) reads another mask's slot.
- **Literature.** Refuter searched for pairing or repeated-number results on Catch-Up: none found. Could not read the MPRA and Feng PDFs' text.
- **Metric.** A1: untested → the pair rule fails at the smallest universe (R ⊆ {1..2}), for windows up to w = 4.
- **Meaning.** The kill criterion of A1 is met (O4): a pair's effect depends on R globally, because after one number of the pair is taken the other stays behind as a large single number. Twins cancel, but intervals have no twins, and the Lean definition uses sets, so the twins fact is a side result.

### 2026-10-22: fixed pick rules lose from N = 4 (A3)

- **Claim / question.** B4. Does a simple pick rule (a function of numbers left and gap) hold the draw against a perfect opponent?
- **Approach.** `solver/src/bin/strategy_eval.rs`: `cargo run --release -p catch-up --bin strategy_eval -- 20` (3 s; output `scratch/strategy_eval-20.md`). Two tables over all positions of {1..N}: the rule player to move, the perfect player to move. Perfect-vs-perfect checked against `Solver` (values, 5,000 random positions per N ≤ 18); rule tables against a memo-free recursion (every position, N ≤ 9). Rules: Largest, Smallest, SmallestCatch (smallest number ≥ gap), Exact (the gap itself if left), LeadOne (gap + 1 if left), StayBehind (largest number below the gap).
- **Outcome.** At every N from 4 to 20, each rule loses as player 1 and lets player 1 win as player 2. At N = 3 all six draw as player 1; as player 2 only Largest holds.
- **Refuter.** SURVIVES. Code audit clean; two independent re-implementations (whole-turn best responder N ≤ 15, explicit opening N ≤ 20) reproduce the whole table. Notes: the in-file recursion shares the table's encoding, so it checks code, not rules; the binary reports values, not how fast a rule loses.
- **Literature.** Refuter: the original paper (MPRA 108784, §3) simulates whole-turn heuristics (MaxScore, MinScore, UseMostNums, …) against each other on {1..10}, not against optimal play. Nothing else found.
- **Metric.** A3: no evaluator → best rule fails at N = 4 (holds N = 3 only).
- **Meaning.** A perfect opponent exploits any fixed greedy rule at once; a drawing strategy must react to the position's structure. Patching fixed rules one failure at a time is aimless without a region to steer into (A2).

### 2026-10-22: interval rows break the parity rule only at small and large gaps (A2)

- **Claim / question.** B2, first part: where do positions break the parity rule (Loss if g > sum(R); else Draw at draw parity g ≡ sum(R) mod 2, else Win)? Rows R = {1..m} and, for even totals, the positions after an opening, R = {1..m} ∖ {x}, over every gap up to sum(R); then every R ⊆ {1..22} at moderate gaps.
- **Approach.** `solver/src/bin/interval_rows.rs`: `cargo run --release -p catch-up --bin interval_rows -- 22` (7 s, 1 GB; output `scratch/interval_rows-22.md`, census `scratch/interval_rows-census-22.md`). Own table over all R ⊆ {1..22} and all gaps ≤ sum; checked against `Solver` on every R ⊆ {1..12} at gaps ≤ 12 and on value({1..N}), N ≤ 22.
- **Outcome.**
  - Rows: every deviation is a Loss at a win-parity gap g ≤ 4 or a Win at a draw-parity gap. Draw-parity gaps are never Losses, so an opening gap (draw parity when the total is even) is a Draw or a Win. Between the Loss zone and the first Win the parity rule is exact; the first Win comes at 0.14–0.30 of sum(R) for m ≥ 12, and above it Wins and Draws still alternate in stretches before a solid Win block ({1..12}: W at 16, D at 18–24, W from 26). V(R, sum R) is always D (take everything, tie).
  - Every opening draws for even-total m = 12–22 (and 23–24 with gaps ≤ 110, refuter); it fails at m = 3, 4, 7, 11 ({1..11} ∖ {10} at gap 10 is a Win).
  - Census over all R ⊆ {1..22}, draw parity, 5 ≤ g ≤ sum/6: complete R has 1,922,656 non-draws among 6,326,766 positions (smallest {1,2,4,8,16} at g = 5, a Win). By holes (max(R) − |R|) at 5 ≤ g ≤ sum/12: none for ≤ 2 holes, 10 of 31,581 at 3, 130 of 115,923 at 4, then fast growth.
- **Refuter.** Strategy part: see the entry above. Rows: data SURVIVES (an independent DP matches all 138 rows over every gap; spot values hand-confirmed); my first wording ("Wins from a threshold of sum/6 to sum/4 upward") BROKEN, corrected above. Every opening drawing for m = 12–22 SURVIVES. The in-file `Solver` check covers gaps ≤ 12 only; the independent DP covers the rest. Census refuted with the near-interval run (log 2026-10-22: near-intervals draw).
- **Literature.** Refuter: nothing on position values against gap parity (MPRA 108784, OEIS A278587, von Stengel's abstract, Feng's thesis).
- **Metric.** A2: no candidate → candidate class "near-interval, draw parity, gap 0 or 5 ≤ g ≤ sum/12" (soundness: log 2026-10-22: near-intervals draw; closure untested).
- **Meaning.** Interval positions are draws in a wide middle band of gaps. A mover trailing by very little sometimes does worse than the parity rule (losses at gaps ≤ 4 where it predicts a win); one trailing by a lot does better (wins where a draw is possible). Completeness is far too weak to keep the band; few holes is the right density notion (log 2026-10-22: near-intervals draw).

### 2026-10-22: parity law proved and formalized (A2)

- **Claim / question.** L3: valueAux R a b f = draw ⇒ a + b + sum(R) even; corollary value S = draw ⇒ sum(S) even.
- **Approach.** Paper proof by strong induction on |R| over the cases of `valueAux` (blueprint L3), after a first version failed review. Lean: skeleton with `sorry`, then proofs, in `lean/CatchUp/Parity.lean`, imported in the library root; `lake build --wfail`, `#print axioms`.
- **Outcome.** Proved: `CatchUp.parity_law`, `CatchUp.even_sum_of_value_eq_draw`. Build clean; axioms propext, Classical.choice, Quot.sound only.
- **Refuter.** First version: BROKEN. Its play-level clause ("final difference ≡ gap + sum left") is false, since the can't-catch-up rule ends games with numbers untaken (valueAux {1} 0 5 false = loss), and its proof argued about one play, not the value. With the gap b − a in ℕ the statement is false (R = {4,5,6}, a = 3, b = 0). Corrected version: SURVIVES (every case audited; each step checked on R ⊆ {0..9}, a, b ≤ 24, both flags, 1,280,000 positions); the refuter's scratch Lean check became the library proof.
- **Literature.** Refuter: the original paper (MPRA 108784, §2.6) states the fact for plays from {1..N} (odd totals can't split evenly), not for the value function; no other proof found.
- **Metric.** A2: unchanged (a tool, not a class).
- **Meaning.** A first reusable Lean lemma about the game, and the Lean infrastructure (unfolding `valueAux`, the `best` fold, the erase/sum bookkeeping) that later game lemmas need. It is a known fact, not a result.

### 2026-10-22: near-intervals draw (A2)

- **Claim / question.** Robustness of the conjecture: are sets close to {1..m} draws? R = {1..m} ∖ H, H ⊆ {1..m−1}, h = |H| ≤ 4. (a) L4: fresh games (gap 0), even sum. (b) L5: draw-parity gaps 5 ≤ g ≤ sum(R)/12.
- **Approach.** `solver/src/bin/near_intervals.rs`: `cargo run --release -p catch-up --bin near_intervals -- 30` (76 s, ~3 GB; output `scratch/near_intervals-30.md`). One layered table on {1..30}, gaps ≤ 30; the full set's row by the recurrence from layer 29. At U = 22 it reproduces `interval_rows`'s gap-0 and holes census exactly (a different DP); printed non-draws re-solved with `Solver`.
- **Outcome.**
  - (a) For 14 ≤ m ≤ 30 every even-sum near-interval with h ≤ 4 draws (71,204 sets at h = 4). Exceptions only at small m: the last at m = 3, 6, 10, 13 for h = 1–4, all first-player wins.
  - (b) h ≤ 2: no exception (35,469 positions at h = 2). h = 3: 10, the last at m = 15; h = 4: 131, the last at m = 23 ({1..6} ∪ {11..23} at g = 20, a mover win); block holes are the worst case. Complete sets fail at moderate gaps (log 2026-10-22: interval rows).
- **Refuter.** SURVIVES. Two engines of its own (a literal `valueAux` port; a layered DP with its own ranking, computing the full set's layer directly) reproduce every count and exception. Coverage caveat: for m = 27–30 the run tests g ≤ 30, short of sum/12 (≤ 38); the refuter's uncapped run finds draws at all 65,772 skipped positions with h ≤ 4. Extra (refuter scratch): L4 holds at m = 31; for h ≤ 2 the first non-draw gap is ≥ 1.17 · sum/12 (≥ 1.44 for m ≥ 16); last gap-0 exceptions at m = 14 (h = 5) and m = 17 (h = 6).
- **Literature.** Refuter: nothing on Catch-Up for sets other than {1..N} beyond the paper's multiset example. A 2024 Brams article (Open Access Government) says sets of 2–20 numbers with an even sum draw; false for arbitrary sets ({2}, {1,3}, {1,4,5,6} are first-player wins), presumably meant for {1..n}.
- **Metric.** A2: candidate C_h sound for h ≤ 2 on m ≤ 30 (from "soundness untested"); closure untested.
- **Meaning.** The conjecture is robust: deleting a few numbers below the top keeps the draw once m is large enough, with a threshold that grows by about 3 per hole. So a proof can't depend on the exact interval; few holes is the right density notion, completeness the wrong one.

### 2026-10-22: hole threshold up to six holes (A2)

- **Claim / question.** B7: how does L4's last exception grow with the number of holes?
- **Approach.** `near_intervals` with MAX_HOLES = 6: `cargo run --release -p catch-up --bin near_intervals -- 30` (64 s; output `scratch/near_intervals-h6-30.md`). h ≤ 4 rows identical to the previous run.
- **Outcome.** Fresh games: h = 5: 88 non-draws of 296,912, the last at m = 14; h = 6: 213 of 1,018,103, the last at m = 17; none for m ≥ 18 up to 30. Thresholds m0 = 3, 6, 10, 13, 14, 17 for h = 1–6. Moderate gaps: h = 5: 1,082 exceptions up to m = 27; h = 6: 7,229 up to m = 30 (the band shrinks with more holes; block holes worst).
- **Refuter.** Not run on this run; the near-interval refuter's own engine had computed the same h = 5, 6 gap-0 figures independently (88 / last m = 14; 213 / last m = 17).
- **Literature.** Not searched (covered by the previous entry).
- **Metric.** A2: unchanged.
- **Meaning.** The gap-0 threshold grows by about 3 per hole, so "near-interval draws" holds for |H| up to about m/3 in this range; the moderate-gap band is less robust (exceptions up to m = 30 at h = 5, 6).

### 2026-10-22: holes grow under drawing play; adjacent pairing holds longest (A2)

- **Claim / question.** B6: on even-total {1..N}, can a defender D, keeping at least a draw, keep few holes at its own turn starts until a bounded endgame? Four measures: holes below max (max − |R|), internal holes (max − min + 1 − |R|), broken adjacent pairs ({2j−1, 2j}; for odd N {2j, 2j+1}, 1 alone), broken mirror pairs ({k, N+1−k}).
- **Approach.** `solver/src/bin/hole_game.rs`: a min-max game, D minimizing c(h) = the most numbers left at a turn start of D with more than h holes that the attacker can force; the attacker makes drawing picks, or any legal pick (`any`). Runs: `hole_game 20`, `hole_game 20 any`, `hole_game 24 Adjacent`, `hole_game 24 any Adjacent` (≤ 4 min each, ≤ 7 GB; outputs `scratch/hole_game-left-*.md`). Checked: values against `Solver` (N ≤ 12), tables against a memo-free recursion (N ≤ 8). A first version measured max(R) at the violation instead of numbers left; it misread "late" as "early" (refuter).
- **Outcome.**
  - Holes below max break almost at once (N = 20, h = 6: 11 numbers left).
  - Internal and mirror holes: c(h) for fixed h grows with N (internal h = 3: 0, 2–3, 6, 9 left at N = 11, 12, 16, 20).
  - Adjacent pairs, drawing attacker: c(2) = 0, 5–6, 8, 10–11 at N = 12, 16, 20, 23–24; c(3) = 0 up to N = 20, 4–5 at N = 23–24; c(4) = 0 up to N = 24. Unrestricted attacker: c(3) = 4 at N = 19–20, 6 at N = 23–24; c(4) = 0.
  - Optimal lines (`hole_game 16 line Adjacent 2 3`): D mostly answers with the partner, each exchange shrinking its lead by 1, and pairs broken early are repaired later by the attacker's own picks.
  - Three pick rules that repair broken adjacent pairs (`strategy_eval 22`) still lose: the best hold N = 3, 4 as player 2 only.
- **Refuter.** Tables SURVIVE (an independent top-down implementation reproduces all 448 cells, N ≤ 20). First reading BROKEN: c measured max(R), not time; corrected above. Also: positive Adjacent bounds hold only against a drawing attacker (an unrestricted one raises the thresholds by 1, through endgame lines); checking right after D's own turn instead gives thresholds one lower for N ≤ 16; the A2 reduction in `lines.md` named the wrong closure condition (fixed). Repair rules: refuter pending.
- **Literature.** Refuter: no pairing or invariant strategy for Catch-Up or similar games found (OEIS A278587; searches on pairing, strategy stealing, "lead alternates").
- **Metric.** A2: closure untested → bounded-hole classes fail closure: for each measure and fixed h the violation point c(h) grows with N (O5).
- **Meaning.** A defender can keep the set close to paired until late in the game, but the defects it must allow grow with N (adjacent pairs: about N/6 for the whole game). A fixed-bound class plus a bounded endgame is ruled out; a class must let defects grow, or measure them by something that does stay bounded (their weight, or the gap they cost).

### 2026-10-22: answering with the partner is not a strategy (A2)

- **Claim / question.** B8: when the attacker's turn ends with y and y's adjacent partner p is left, is taking p a drawing reply for the defender?
- **Approach.** `solver/src/bin/partner_reply.rs`: `cargo run --release -p catch-up --bin partner_reply -- 24` (30 s, ~1 GB; output `scratch/partner_reply-24.md`). Over every drawn turn start (R, g) and every y ∉ R with y ≥ g whose partner p is left: is p a drawing pick? By broken pairs, by numbers taken, by the opponent's new gap p − g. Values checked against `Solver` (N ≤ 12).
- **Outcome.** A reply that doesn't end the turn (p < g) draws in all but a handful of cases. A turn-ending reply fails in 50%, 44%, 35%, 26% of all such positions at N = 12, 16, 20, 24. In the opening turns (≤ 3 broken pairs, ≤ 3 taken) it draws in 80%, 98%, 100% at N = 12, 16, 20–24.
- **Refuter.** Tally SURVIVES (independent re-tally matches at N = 7–23). BROKEN: "non-ending failures only with ≥ 4 broken pairs" (N = 23 has three with 3, reachable in drawing play: R = {2,6,12,13,16,17,20,22,23}, g = 3, y = 3, where only 12, 13, 16 draw). Decisive: in a game where D must start every turn with the partner and plays perfectly otherwise, an attacker that never blunders wins from N = 11 (D = player 1) and 12, 15, 16 (both); an attacker allowed losing picks wins from N = 7. Weighted by random drawing play, the "large new gaps fail" pattern mostly disappears, and failing partner replies per game stay ≈ 0.7 at N = 12–20. The repair-rule losses (`strategy_eval 22`) come from their fallbacks, not the repair step.
- **Literature.** Refuter: no pairing or partner strategy for Catch-Up found.
- **Metric.** A2: unchanged (no class); A3: forced partner reply plus perfect play fails from N = 11.
- **Meaning.** Drawing play resembles adjacent pairing, but a pairing rule is not a strategy: the defender must sometimes refuse the partner, also with one broken pair and a small gap, and the attacker steers into those positions in the middle game (O6). Per-position statistics over all positions overstate safety; strategy claims need a game where the rule is enforced.

### 2026-10-22: best by membership formalized; endgames with two numbers proved (A2)

- **Claim / question.** B5: L6 (`best` is win iff a win is listed, draw iff a draw and no win) and L7 (exact values with ≤ 2 numbers left, mover trailing by g).
- **Approach.** Paper proofs in the blueprint; Lean for L6 in `lean/CatchUp/Best.lean` (skeleton, then proofs), imported in the library root; `lake build --wfail`, `#print axioms`. L7 not yet formalized.
- **Outcome.** L6 formalized (`Outcome.best_eq_win_iff`, `_draw_iff`, `_loss_iff`); build clean, axioms within propext, Classical.choice, Quot.sound. L7: {a, b} with a < b is decided by comparing g + a with b when g ≤ a, and g with a + b when g > a; paper proof.
- **Refuter.** L6: SURVIVES (every list ≤ 7 from every start). L7 first proof: BROKEN (the split "a < g ≤ b: win" fails at a = 0, g = b, where the value is a draw; the statement held on 104,050 positions); repaired proof: SURVIVES (71,652 positions, each step).
- **Literature.** Refuter: Feng's thesis covers 3–4 numbers only; the original paper has informal endgame remarks only.
- **Metric.** A2: unchanged (tools).
- **Meaning.** Makes the order of `attach.toList` irrelevant in Lean proofs, and gives the first endgame formulas; L7's Lean proof is next in line for formalization.

### 2026-10-22: when the partner must be refused has no simple rule (A2)

- **Claim / question.** B9: in play where D answers with the partner whenever that still draws, which reached turn starts force D to refuse the partner, and what separates them?
- **Approach.** `solver/src/bin/partner_game.rs`: `cargo run --release -p catch-up --bin partner_game -- 20` (36 s; output `scratch/partner_game-20.md`). Explores every reachable state (bitsets), attacker making any drawing pick; tallies D's turn starts with the partner left. Checks: values against `Solver` (N ≤ 12); the refuter's N = 11 refusal is found.
- **Outcome.** Refused in 40% of distinct reached cases at N = 11, 26–30% at N = 20. Replies right after a tie that don't end the turn are never refused. Turn-ending refusals rise with r = (p − g) / sum(R ∖ p) (N = 20, player 1: 11%, 29%, 48%, 65%, 72%, 67%) with no threshold; the partner is the only losing pick in just 8–10% of refusals.
- **Refuter.** SURVIVES (independent re-implementation reproduces every count at N ≤ 16). Caveats: the shares count distinct states, and weighted by random drawing play they drop to 5–15% (0.16–0.40 refusals per game); "continuing replies" is only the reply right after a tie; the r trend dips in the last bucket. Best separator without values: gradient boosting on 44 cheap features, error 0.235 against a 0.36 baseline; best simple rule (depth-4 tree) 0.311; the count of numbers left above the opponent's new deficit is the best single feature (0.323). With values, "the deficit falls outside the opponent's draw band" reaches 0.12. Adjacent pairing with n alone, or mirror pairing, doesn't help.
- **Literature.** Not searched (covered by the earlier entries).
- **Metric.** A2: unchanged.
- **Meaning.** Whether to refuse the partner is a question about where the opponent's new deficit lands in its draw band, which depends on the whole set; no cheap feature predicts it. Together with O5 and O6 this nearly meets A2's kill criterion; a new idea is needed.

### 2026-10-22: sets made of adjacent pairs draw (A5)

- **Claim / question.** Ideator idea (fresh-idea unit). L8: (E) every S whose maximal runs of consecutive numbers all have even length (S = p disjoint pairs {x, x+1}) has V(S, p mod 2) = draw; (T) the same for {1,2,3} ∪ (an E set above 3), p = its pairs. {1..N} is E at gap 0 for N ≡ 0 mod 4 and T at gap 0 for N ≡ 3 mod 4, so L8 implies L1.
- **Approach.** `solver/src/bin/pair_sets.rs`: `cargo run --release -p catch-up --bin pair_sets -- 30` (71 s, ~3 GB; output `scratch/pair_sets-30.md`, SHA-256 1049e6a8…). One layered table on {1..30}; every member with max ≤ 16 matches `Solver` at every draw-parity gap ≤ its max; at U = 20 it reproduces the ideator's independent counts (5,472 / 5,473). Independent DP without the crate (`scratch/pair_sets_indep/main.rs`, DP from `scratch/ideator/eap2.rs`): same result on {1..26} (196,417 E, 46,368 T sets).
- **Outcome.** No exception: all 1,346,268 E sets and 317,811 T sets ⊆ {1..30} draw at g0, including sparse ones ({1,2,29,30}). Not robust at other gaps: sparse E sets fail already at g0 + 2 ({26,27,29,30} at gap 2); 426,644 E sets draw at every draw-parity gap ≤ min(sum, 30). Ideator (unchecked): E positions at g0 are not closed under play ({1,2,3,4}, attacker takes 2: no reply returns to an E set at its g0); pairs {x, x+d} with one common d and APs of length 4k also draw; |M({1..N}, 0)| ≤ 1 (final margin) for N ≤ 23.
- **Refuter.** Not run (user stopped for usage); the independent DP is the check so far.
- **Literature.** Ideator: nothing on Catch-Up beyond Known; balancer and discrepancy games are asymptotic only.
- **Metric.** A5 (new): G1' proved for p ≤ 1 (L7 at {a, a+1}, gap 1), checked to U = 30.
- **Meaning.** A sharper statement than L1 that holds on very sparse sets, so a proof must rest on the pair structure, not density (unlike L4, A4). Heuristic: a pair = twins (which cancel by mirroring) plus a unit offset; p units at gap p mod 2 draw. The forced partner reply still fails (O6), so the proof needs a larger class than (E, g0).

### 2026-10-22: far-apart pairs proved (A5)

- **Claim / question.** B11. For S = p pairs P_i = {a_i, a_i + 1} with a_1 ≥ p and a_{i+1} > sum(P_1 ∪ … ∪ P_i) + a_i + 1: V(S, g) = f_p(g) for g ≤ a_1, where f_p(g) = draw if g ≤ p and g ≡ p (mod 2), win if g < p and g ≢ p, loss if g > p (blueprint L9). At g = p mod 2 this is L8 (E) for these sets.
- **Approach.** Paper proof (blueprint L9): a value G(L, g; f) where f replaces "draw at 0, loss above" as the payoff when L runs out; opening the top pair while a smaller number is left loses, since the opponent then takes everything below along with the partner, so the top pair only changes f; each pair turns f_j into f_{j+1}. Check: `solver/src/bin/far_pairs.rs`, `cargo run --release -p catch-up --bin far_pairs` (1 s; output `scratch/far_pairs.md`): minimal sequences of the regime for p ≤ 7, and every pair set with p = 2, 3, 4 (max ≤ 80, 60, 40) by which hypotheses hold; V(S, 0) cross-checked with `reference_value` for p ≤ 4.
- **Outcome.** Proved on paper and matched in every tested case: rows g ≤ a_1 for p ≤ 7 (largest number 28,198). Every 2- and 3-pair set in which each pair exceeds the sum below it matches f_p at g ≤ min(p + 1, a_1). Mechanism: pairs are opened from the bottom, each opened and closed in consecutive turns.
- **Refuter.** SURVIVES (proof mode): every step checked with its own engine, including (P2) on random arbitrary sets L (389,848 cases) and the full statement on 1,650 random sequences with p ≤ 7. Two wording fixes (a gap-0 turn ends with a lead equal to its pick; m ≥ 0 made explicit), applied. My note that (A) looks unnecessary was wrong: {1,2,4,5,13,14,40,41} at g = 1 is a loss where f_4 says win (all such failures have a_1 = 1, none at g0). Under F0 alone (P2) fails, so weakening (F) needs another induction.
- **Literature.** Refuter: nothing on Catch-Up for super-increasing or pair sets.
- **Metric.** A5: L8 proved for p ≤ 1 → also for far-apart pair sets with any p.
- **Meaning.** An infinite family of L8 instances, and a picture of why pairs act as tempo units: each pair flips the parity of the drawn gaps and widens their range by one. It says little about {1..N} directly, where pairs are dense and the high pairs are not protected; but it hands A5 the tool of a modified final payoff.

### 2026-10-22: pair sets, first picks; two pairs proved (A5)

- **Claim / question.** Which first picks draw in pair sets at g0 (E, and T = {1,2,3} ∪ E')? Does a partner-reply defence prove "≤ draw" by induction on p? Prove L8 at p = 2 (B12).
- **Approach.** `solver/src/bin/pair_moves.rs`: `cargo run --release -p catch-up --bin pair_moves -- 28` (25 s; output `scratch/pair_moves-28.md`): one layered table on {1..28}; pick values neg V(S − x, x − g0) by role; V(E, g0 + 2j), j ≤ 3. Members with max ≤ 14 re-solved with `Solver` pick by pick. Paper proofs from L6, L7 (blueprint L10, L11).
- **Outcome.**
  - T (121,393 sets): picks 1 and 3 always draw; pick 1 leaves the opponent in the pair set {2,3} ∪ E' at its g0 (L10 (a)), so T's "≥ draw" follows from E's "≤ draw".
  - E (514,228 sets): no pick role always draws; a_1 + 1 fails in 2,498 sets, all dense high blocks ({23,…,28}: only 26, 27, 28 draw).
  - Partner replies: for p even, "≤ draw" follows from L8 at p − 1 (L10 (b)). For p odd, a bottom pick answered by its partner leaves the mover at gap 2 with an even number of pairs, a mover win in 446 sets (smallest {2,3,4,5}: pick 4 wins), so no partner induction.
  - L11: every 2-pair set draws at gap 0 (≤ by L10 (b) and L7; ≥ by the pick a + 1).
- **Refuter.** L10, L11 (proof mode): SURVIVES; own DP and a literal port, (b)'s partner inequalities on every R ⊆ {1..26} (419M checks), L11 for all b ≤ 61; it reproduced `pair_moves` at U = 22 exactly. Notes: the early-loss check of `valueAux` must be shown not to fire, and a Lean version needs "V depends only on the deficit" (added to the proofs).
- **Literature.** Refuter: nothing on pair sets or partner strategies for Catch-Up.
- **Metric.** A5: L8 proved for p ≤ 1 and far-apart pairs → also p = 2 for all sets.
- **Meaning.** Reductions inside L8 work for p even and for T, but the odd-p upper bound needs replies other than the partner (O6 again). The next entry shows L8 itself is false.

### 2026-10-22: pair sets do not all draw (A5; corrects 2026-10-22: sets made of adjacent pairs draw)

- **Claim / question.** L8 (all pair sets draw at gap p mod 2), claimed from `pair_sets 30` with no exception among sets ⊆ {1..30}.
- **Approach.** Refuter (claim mode): audit of `pair_sets.rs`; an independent full-table DP; memoized and whole-turn engines on sparse sets with max up to 200; exhaustive and random hunts. Re-checked here with the crate's `Solver` (`scratch/l8check/`).
- **Outcome.** False just above the tested range. C = {17,18,20,21,25,26,28,29,31,32} (p = 5): V(C, 1) = loss for the mover. {1,2} ∪ C (p = 6): player 1 wins, only by opening 2; {1,2,3,4,5} ∪ C (T, p = 6) and {1,2,3} ∪ C at gap 1 (T, p = 5) fail too. E with p = 5 and max ≤ 44 has 232 exceptions, all losses with min ≥ 17; random pair sets with p = 5–8 and max 100–200 fail in about 0.5–1%. None found with p ≤ 4 (E exhaustive: p = 3 with max ≤ 200, p = 4 with max ≤ 80).
- **Refuter.** BROKEN. `pair_sets.rs` is correct (enumeration complete, table exact at every gap ≤ U, the full set handled); the error was concluding from a universe that stops at 30. The reduction L8 ⇒ L1 and value(S) = V(S, 0) are correct (checked on all subsets of {1..26}).
- **Literature.** Refuter: nothing on Catch-Up for pair sets.
- **Metric.** A5: kill criterion met (a counterexample to L8).
- **Meaning.** The claim "a proof must rest on the pair structure, not density" is wrong: the exceptions are exactly the sparse, high pair sets. Pair structure alone does not force a draw; density matters too, as in L4. L9, L10, L11 stay true. Every exception found has a sparse part high up (the p = 5 cores have min ≥ 17), and adding small pairs below does not repair it ({1,2} ∪ C); pair sets with few holes, as in L4, may still draw.

### 2026-10-22: aligned pair sets do not all draw either (—)

- **Claim / question.** Partner exchanges from {1..N} only remove the aligned pairs {2j−1, 2j}, so the sets they reach are aligned pair sets. Do all aligned pair sets draw at gap p mod 2? That would give a class closed under partner exchanges, unlike L8 (O7).
- **Approach.** Filtered the refuter's list of exceptions (`scratch/refuter/l8/hunt-E5-31-44.txt`: every pair set with p = 5 and max 31–44) for sets whose pair bottoms are all odd; re-solved the hits with `Solver` (`scratch/l8check/`).
- **Outcome.** False. 2 of the 232 exceptions are aligned: {21,22,25,26,31,32,35,36,39,40} and {23,24,27,28,33,34,37,38,41,42} are losses at gap 1, and with {1,2} added both are player-1 wins at gap 0. Both are sparse and high, like the rest of O7.
- **Refuter.** Not run (a filter of refuter-checked data, re-solved with `Solver`).
- **Literature.** Not searched.
- **Metric.** — (no main line; a candidate line killed before it started).
- **Meaning.** No pair-structure class closes on its own: the partner-reachable family contains sparse, high sets that are not draws. Any class must also bound sparseness, and the defender must steer away from sparse sets rather than answer with the partner.

### 2026-10-22: line review, new lines (A6, A7)

- **Claim / question.** With every line dead or shelved, which new lines does the evidence support? Ideator (max effort), called for the review.
- **Approach.** Ideator's own scratch DPs (`scratch/ideator/r2/`, 30 s–2 min each, ≤ 1 GB); its counterexample to the low-change law re-solved with `Solver` (`scratch/l8check/`).
- **Outcome.** Kept: A6 inert top quadruple (a defender that never opens {N−3..N} first draws every even-total N ≤ 24 in both roles; 3+ reserved top pairs lose); A7 even blocks {a..a+2p−1} at any height (draw at g0 for p ≤ 6, a ≤ 60; row t_p for a ≥ 12); low-change law for A4 (B22): adding {1..k} cures an O7 core at a sharp k near 1+…+k ≈ 2·min C, but {1..9} ∪ {25,26,28,29,36,37,39,40,43,44} is a player-2 win (confirmed); margin bound M(R, g+1) ≥ M(R, g) − 1 on R ⊆ {1..16} (B21). Dropped, each losing in the ideator's runs: keeping the low block {1..k} for last (every k, N = 7–20); a run-parity defender (any pick restoring even runs) from N = 15–16, so O6 extends to flexible re-pairing; greedy defenders by random-continuation potentials (by N = 7); any fixed bound on the attacker's debt (paper argument). |M| ≤ 1 at every opening of {1..N}, N ≤ 20.
- **Refuter.** Not run (ideas and unchecked scratch data; each line's first unit checks its own claim).
- **Literature.** Ideator: nothing beyond Known; scoring-play surveys (arXiv 1202.4653, 1107.5092) not opened, none treats this turn rule.
- **Metric.** — (new lines; A6 main by evidence: closest to {1..N} and a cheap kill test).
- **Meaning.** Two new routes: A6 treats the top four numbers like L9's far pairs (a final payoff), A7 works in a two-parameter family that contains {1..N} and has a provable end at large a. Density matters (O7, B22), and pairing rules fail as strategies in every form tried.

### 2026-10-22: low change cures sparse cores, without a clean law (A4)

- **Claim / question.** B22. For an O7 core C (5 pairs, not a draw at gap 1), how large must k be for {1..k} ∪ C to draw at its draw-parity gap? Is there a law in min C (ideator: 1+…+k ≈ 2·min C)?
- **Approach.** `solver/src/bin/low_change.rs`: `cargo run --release -p catch-up --bin low_change -- 6 20 1` (40 s; output `scratch/low_change-6-20.md`). Regenerates the failing cores with max 31–44 (232, as the refuter found), profiles every 6th (39) and 20 random failing cores with numbers 13–60; one layered table on {1..12} ∪ C per core, gives V({1..k} ∪ C, g0) for k ≤ 12.
- **Outcome.** For k = 0..7 the profile is L W W L W W W L for every core: the value depends on k alone, as if C were a fixed final payoff for the game on {1..k} (L9's mechanism). From k(C) on, all draw: k(C) = 8 or 9 for min C = 17–18, 9 for 19–23, 10 for 24, 10 or 11 for 25, 11 for 26–28, 12 or more than 12 for 29–36. 1+…+k(C) lies between 1.96 and 2.7 times min C, and 1+…+(k(C) − 1) between 1.6 and 2.3 times; cores with the same min need different k.
- **Refuter.** Not run (no claim kept: the law fails).
- **Literature.** Not searched.
- **Metric.** A4 (shelved): unchanged.
- **Meaning.** A sparse high part acts as a terminal payoff, and enough low change, about twice its smallest number, restores the draw. The threshold also depends on the rest of C, so "low change ≥ 2·min" is not a characterization. This explains O7 but gives no invariant.

### 2026-10-22: the top quadruple can wait, but not by a local lemma (A6)

- **Claim / question.** B16, B17. (1) Does the defender draw Γ_N (it never takes from the top four numbers T except to close a pair the attacker opened, or when only T is left) for even-total N up to 28? (2) Lemma A: at positions with T intact, does barring the attacker the same way (Γ') leave every value unchanged?
- **Approach.** `solver/src/bin/top_reserve.rs`: own full tables (restricted defender to move, attacker to move), one u64 row per set. `cargo run --release -p catch-up --bin top_reserve -- 3 20 0 1 2 3 4` (1 s) and `-- 23 28 0 1 2 3` (4 min, 4.3 GB at N = 28; outputs `scratch/top_reserve-20.md`, `top_reserve-23-28.md`); `-- compare 7 24 2` (6 s; `scratch/top_reserve-compare-24.md`). Checks: q = 0 equals `Solver` on every set and gap for N ≤ 12; restricted tables equal a plain recursion for N ≤ 8; the table to N = 20 equals the ideator's independent one.
- **Outcome.** (1) Γ_N with the top quadruple (q = 2) is a draw in both roles for every even-total N from 7 to 28, and with one top pair (q = 1) from 3 to 28; three reserved pairs lose (N = 12 as player 2, both roles at 16–28). (2) False: early openings change the value at about 30% of the positions with T intact, even where the gap is payable without T (N = 8: the defender opens 4, the attacker takes 1 and, 3 behind with {2,3,5,6,7,8}, wins in Γ by taking 7 but only draws in Γ').
- **Refuter.** (1) SURVIVES: two independent engines of its own (a literal Python `valueAux` with history, and a bitset retrograde) reproduce every cell, N = 27, 28 included; Γ' openings also draw at 27, 28. (2) SURVIVES with caveats: counts reproduce for N ≤ 24; my N = 7 example ({1..7} at gap 1) is unreachable; reachable differences start at N = 8; among positions reachable in Γ at N = 24, 7.4% (defender to move) and 58.1% (attacker to move) differ. Along the defender's value-keeping play, every difference is "Γ draw, Γ' attacker loss": the attacker opens early only to save a lost game, never to win.
- **Literature.** Refuter: nothing on reserved-top strategies for Catch-Up.
- **Metric.** A6: largest N with Γ_N drawn: 24 (ideator, unchecked) → 28, checked by two engines.
- **Meaning.** The defender can always leave the top four numbers for last, to N = 28. But Lemma A has no local form, so the split into Lemmas A and B fails (O8); a proof would need an invariant tied to the defender's play, the same obstacle as A2's closed classes.

### 2026-10-22: even blocks draw at every height, but the band can shrink (A7)

- **Claim / question.** B19. For blocks B(a, p) = {a..a+2p−1}: (1) TI, V(B, p mod 2) = draw; (2) from which height a0(p) the row at g < a is t_p (draw at draw-parity g ≤ p, win at 0 for p odd, loss otherwise); (3) does the drawn band always contain every draw-parity g ≤ p (A7's descent route)?
- **Approach.** `solver/src/bin/block_rows.rs`: `cargo run --release -p catch-up --bin block_rows -- 8 80` (5 s; output `scratch/block_rows-8-80.md`), `Solver` per block, rows at every gap ≤ max.
- **Outcome.** (1) TI holds for every p ≤ 8, a ≤ 80. (2) a0 = 1, 3, 7, 8, 11, 12, 14, 16 for p = 1..8 (about 2p); below a0 the band widens (draws continue at draw parity past p, wins in between). (3) One miss: p = 2, a = 2, {2,3,4,5} at gap 2 is a mover win, while {3,4,5,6} draws there; so the band shrinks from a = 3 to a = 2.
- **Refuter.** All three SURVIVE (own engine, matched against a literal `valueAux` on 70 blocks and OEIS): TI and a0 also hold to a ≤ 200, and TI for p = 9, 10 (a0 = 17, 19) at a ≤ 80; (2,2) stays the only miss. Wording: a0 is the least height from which every row matches; some lower heights match too.
- **Literature.** Refuter: nothing on blocks at any height.
- **Metric.** A7: unchanged (paper proofs for p ≤ 2); kill criterion met (a band losing part of [0, p], O9).
- **Meaning.** Translated even blocks draw at g0 at every height tested, unlike O7's separated pairs, so TI is a robust conjecture containing L1 (N ≡ 0 mod 4). But the band is not monotone in the height, so a descent from large a to a = 1 has no simple invariant.

### 2026-10-26: high blocks reduce to a rounds game; pair sets fit t_p at debts 0 and 1 (A7)

- **Claim / question.** B20. (1) On {a + o : o ∈ O} with a large, Catch-Up is the rounds game R(O, d): each round the player behind picks one offset, then the other picks one; a tie keeps the mover (definitions: `scratch/b20/NOTES.md`). (2) T1: R({0..2p−1}, d) = t_p(d). (3) Which simpler laws hold, as footholds for a proof?
- **Approach.** Python in `scratch/b20/` (scratch; started by an unrecorded session this morning, its runs re-checked here): `rounds.py 6` (R equals the literal offset game on even subsets of {0..7}, d < 12; T1 for p ≤ 6, d ≤ p + 1), `xmax.py 8`, `maxpick.py 8` (31 s together); new: `pair01.py 5 17`, `pairband.py 5 16`, `laws.py 10`, `margin.py 10`, `rules.py 4 13` (each < 2 min).
- **Outcome.** (1) Exact when a > g + sum(O), since every debt reached is ≤ g + sum(O); for blocks a > g + p(2p−1) (a sufficient bound; the measured a0 ≈ 2p). (2) T1 holds for p ≤ 6; the mover taking the max when first already reaches t_p for p ≤ 8, though the max is not optimal in general (68 of 2032 positions within {0..7}). (3) T2: every pair set (p disjoint pairs {x, x+1}, any spacing) has R = t_p at debts 0 and 1 for p ≤ 5, offsets < 17; at d ≥ 2 pair sets lose part of the band, depending on run lengths and gaps. Law 1: the player moving first at a tie never loses, on every even O within {0..9}, even in margin form. On paper: U0, R(O, d) = L for d > c(O), the bottom-up matching cost (partner answers), which gives t_p(d) = L for d > p; parity reduces T1 to "≥ draw" and "≤ draw" claims. No general law: R(O, d) is not monotone in d, and fixed pick rules for one player all fail on pair sets (the leader at debt 1, p even, must refuse the partner).
- **Refuter.** Claim mode (2026-10-26, own Rust code): the reduction SURVIVES (literal `valueAux` port, 866k comparisons, 0 mismatches; the debt bound must be argued cumulatively: the mover's deficit is g plus a signed sum of distinct offsets; a = g + sum(O) also works); T1 SURVIVES for p ≤ 13 at every debt; T2 SURVIVES for p ≤ 13 within {0..25} and for spacings up to 200 (p ≤ 4) … 30 (p = 9); U0 SURVIVES (argument checked, 184.5M cases); Law 1 BROKEN (see next entry, O10).
- **Literature.** Refuter: arXiv API and web searches for the game, for "behind picks first" rules and for catch-up picking sequences in fair division found nothing beyond the README's sources.
- **Metric.** A7: unchanged (paper proofs for p ≤ 2).
- **Meaning.** High blocks are a clean finite game, so B20 is now a statement about one game on offsets. T2 is stronger than TI at large heights and contrasts with O7: pair sets fail L8 only at low heights. A proof needs a class closed under play; pair sets are closed under partner answers but not under the first picker's opponent breaking pairs, which is where the work is.

### 2026-10-26: rounds game tables to 24 offsets; the tie law fails (A7)

- **Claim / question.** Push T1 (rows of {0..2p−1} are t_p) and T2 (pair sets fit t_p at debts 0 and 1) beyond Python's range, and test the footholds from the previous entry: Law 1 (the mover at a tie never loses, any even O), the margin bounds μ(O, d) ≥ −d and μ(O, d) ≤ max(c(O) − d, parity bit) (both held within {0..9}), and whether sets with one non-unit matched gap have rows given by a few parameters.
- **Approach.** New experiment `solver/src/bin/rounds_game.rs`: full table of R over every even O ⊆ {0..U−1}, debts d < U (debts ≥ U are losses by U0, since c(O) ≤ U − 1), checked against an uncut recursion for U ≤ 10 (0 mismatches). `rounds_game 24`: 12 s, ~400 MB (output `scratch/rounds_game-24.md`). Counterexample re-checked with the Python code (`rounds.py`, `margin.py`). Python `bounds.py 10`, `onegap.py 11`.
- **Outcome.** T1 holds for p ≤ 12 at every debt. T2 holds for all 28,657 pair sets within {0..23}, and no pair set wins at any debt ≥ 1. Law 1 fails: {0,4,5,6,7,8,10,11} at a tie is a loss with margin −1, the first counterexample, 22,992 within {0..23} (O10); with it μ ≥ −d fails. Within {0..9} the upper bound μ ≤ max(c − d, parity bit) held (not rerun at 24). Rows of one-gap sets depend on where the other pairs sit, not just on (p, g, position of the gap).
- **Refuter.** Not run on this entry separately; the claim-mode run on the previous entry was told Law 1 broke (C4) and asked to confirm it independently.
- **Literature.** Not searched.
- **Metric.** A7: unchanged (paper proofs for p ≤ 2).
- **Meaning.** T1 and T2 are robust (p ≤ 12), but general offset sets carry no law to induct on (O10), and the natural enlargements of pair sets (one broken gap) have unstructured rows. A proof must stay inside a class tied to pairs: e.g. pair sets plus orphans whose partners are gone, tracked by who is owed each orphan.

### 2026-10-26: always taking the largest number draws high pair sets (A7)

- **Claim / question.** T2 at the draw debt g0 = p mod 2 needs, for each player, a strategy that never loses on pair sets. Which strategy, and with what guarantee? Candidate found: always take the largest number left (AM: the final margin of an always-max player is ≥ −1 when it starts as the mover at debt 0 or 1, or as the non-mover leading by any l ≥ 0; with parity, ≥ −1 means ≥ 0 at debt g0, so always-max draws there in both roles).
- **Approach.** Python in `scratch/b20/`: `split.py` (the game in which no one may take both numbers of a pair), `openlow.py` and `trace.py` (opening the lowest pair), `maxrole.py`, `maxmargin.py`, `maxgen.py`, `phi.py`, `phi2.py` (always-max against a perfect opponent; reachable states). New experiment `solver/src/bin/max_strategy.rs`: `max_strategy 22 8` (8 s; output `scratch/max_strategy-22-8.md`), which agrees with `maxmargin.py` for p ≤ 5.
- **Outcome.** AM holds for every pair set within {0..21} (p ≤ 11), with the least margin independent of the set: 0 or −1 by parity, and l − p for a lead l > p. Always-max fails only where parity forces a winner (p odd at debt 0; the leader at debt 1 with p even). The split game equals the real game at debts 0 and 1 (p ≤ 5) but not at debt ≥ 2. Opening the lowest pair loses: the opponent takes both numbers of a higher pair. Always-max does not bound losses on general sets ({0,2,4,5,6,8}: −3). Structure under always-max (p ≤ 4): at most one orphan owed to the opponent (the current max x, right after Z took x+1); with Φ the margin with each orphan credited to the player owed it, Z's picks never lower Φ, final margin = final Φ, and Φ ≥ −1 at every reachable round start.
- **Refuter.** Claim mode (2026-10-26, own code): SURVIVES; all 75,025 pair sets within {0..25} (p ≤ 13), leads ≤ 14, random sets with spacing up to 200 and special families; parity step checked; R(E, p mod 2) = D on all pair sets within {0..17}. Scope: one gap 2 breaks it ({0,2,4,5} at debt 1: always-max −2 where a draw exists); starts at debt ≥ 2 fail (e.g. {0..5} at debt 3). Real game: always-max draws blocks {a..a+2p−1} at g0 in both roles from a = 1, 2, 7, 12, 21, 30, 43, 56 (p = 1..8), i.e. p(p−1) + [p odd].
- **Literature.** Not searched.
- **Metric.** A7: unchanged (paper proofs for p ≤ 2); a candidate lemma (AM) whose proof would give TI for blocks with a > 1 + p(2p−1) and every p.
- **Meaning.** High blocks, and pair sets placed high, have a simple drawing strategy: always take the largest number. That turns B20 into proving one strategy's guarantee rather than computing values, and it explains why spacing does not matter at debts 0 and 1. The proof must handle doubles (both numbers of a pair to one player), since who moves first depends on the actual margin.

### 2026-10-26: toward a proof of AM: a potential and its closure (A7)

- **Claim / question.** Find an invariant that proves AM (always-max Z ends ≥ −1 on pair sets from its starts) by induction over rounds.
- **Approach.** Paper analysis plus checks in `scratch/b20/`: `nodouble.py 6 14`, `phi3.py`–`phi5.py`, `psi.py`, `deltaphase.py` (reachable states, p ≤ 6), `closure.py`/`closure2.py` (closure of a candidate invariant over every round-start state satisfying it, not only reachable ones: p ≤ 5, offsets ≤ 10), `variants.py 5 13`.
- **Outcome.** Established on paper (unchecked): (1) every number Z holds exceeds every number left, so there is at most one pair half-taken by Z, and its remainder x is the largest number left; (2) with Φ = margin + remainders owed to Z − remainder owed to Y, Z's picks change Φ by +1, 0 or +2x, Y's by −1, +1, 0 or −2u (doubling remainder u), and the final margin is the final Φ; (3) at a round start, #remainders owed to Z − #owed to Y = 2δ, δ = Z's doubles − Y's doubles; Y can double while δ = 0 only when Z holds the top half, and Z then doubles x > u at once; so every Y double can be matched to a Z double on a higher pair. Data: Y never gains by doubling (all 1,624 starts, p ≤ 6); reachable round starts have four shapes (no halves; Z's top half + one Y half; δ ≥ 1 with or without Z's top half), Z moves only in the first shape at margin −1 or 0. The invariant "Φ ≥ −1 if δ = 0; Φ − (δ largest 2u) − #fresh pairs ≥ −1 if δ ≥ 1" is closed for p ≤ 4 but not p = 5 (68 violations, all from unreachable states and all with F ≥ −1 afterwards: too crude, not false). Variants of always-max (close owed remainders first; answer with the partner) lose by up to 4.
- **Refuter.** Not run (no complete proof yet); AM itself is with the refuter in claim mode.
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** The δ = 0 part of the proof is a clean walk argument (whoever trails moves and gains one); the open part is the phase after Z doubles, where Z is far ahead but a potential must also bound Y's later doubles. The missing ingredient: a remainder owed to Z that is the largest number left can only be doubled immediately, since Z takes the largest number next.

### 2026-10-26: the always-max proof splits at Z's first double (A7)

- **Claim / question.** Close the proof of AM (L15) by (a) an invariant for the phase where both players have doubled equally often (δ = 0), and (b) a one-shot bound for the phase after Z's unmatched double (δ ≥ 1).
- **Approach.** (a) Invariant: no half-taken pairs, with Z to move only at margin −1 or 0 and Y to move at ≥ 0; or Z's top half plus one Y half, Y to move, Φ ≥ −1, and Φ ≥ 1 when Y holds the low of its pair. Hand case analysis of one round, plus brute-force closure over every state satisfying it (`scratch/b20/closure4.py`: p ≤ 6, offsets ≤ 13, margins ≤ 70; 2.9M states). (b) L14, the greedy bound: whatever the order of picks, an always-max player loses at most c_td(T) (top-down pair gaps) from T on; proved on paper; `greedy.py 10` checks it is exact on every even T ⊆ {0..9}. Entry condition s − c_td(T) ≥ −1 checked on reachable states (`greedy2.py`, p ≤ 6) and by hand.
- **Outcome.** (a) Closed: 0 violations, matching the hand cases (rounds from the no-halves shape lead to it or to the top-half shape; from the top-half shape Y closes x, doubles u (Z doubles x at once, net ≥ +2), or opens a fresh pair, which lets Z double x and starts δ = 1). (b) L14 holds, but the entry condition fails from 7 pairs: from {0..9, 11, 12}, Z holding 13, Y holding 10, Z's margin 2, Y opens 9 and Z doubles 12; then s − c_td = −2 while the true guarantee is 0. L14 lets Y pick first in every remaining round, but once Y doubles back, Z regains the tempo on the low pairs. Also: the refuter's even-total player-1 loss {75,80,81,84,86,88,89,91} re-checked with the new `set_value` binary (Solver and `reference_value`), added to O10.
- **Refuter.** Not run on this entry (L13 and L14 to go to proof mode).
- **Literature.** Not searched.
- **Metric.** A7: unchanged (paper proofs for p ≤ 2). Blueprint: L13–L17 added as conjectures, with proof drafts for L13, L14 and L16 (from L15).
- **Meaning.** AM reduces to bounding the δ ≥ 1 phase. A bound there must give Z back the tempo on pairs below the open remainders, e.g. by applying L14 only to the part of T above them, or by a potential that reserves the costliest δ remainders (J2), which is right on reachable states (p ≤ 6) but not closed by itself.

### 2026-10-26: a paper proof of the always-max lemma (A7)

- **Claim / question.** L15 (always-max ends ≥ −1 on pair sets from its starts) by an argument that survives the phase after an unmatched double; and the refuter's proof-mode verdicts on L13 (reduction) and L14 (greedy bound).
- **Approach.** Ideator (fresh-idea unit, effort max; report in `scratch/ideator/b20/`): measure Φ only at balanced round starts (equal doubles); a stretch between two balanced starts gains Φ ≥ 1 by a pick-counting identity. I re-derived the identity, the matching of doubles and the bound on Z's closes, merged them with my one-round case list, and wrote L15's proof into the blueprint. In parallel `solver/src/bin/round_potential.rs 8 18 120` (11 min; output `scratch/round_potential-8-18-120.md`) tested my round-by-round potential (reserve the δ largest remainders plus fresh pairs above them, one-round lookahead at states with Z's top half).
- **Outcome.** L15 has a complete draft proof: Facts A–C, invariant Φ ≥ −1 at balanced starts, (P1) one-round cases, (P2) ΔΦ ≥ Σ(x_j − w_j) + c − 1 ≥ 1 per stretch. With L13 and parity this gives L16 (every pair set placed above its sum draws at g0), hence TI for blocks with a > 1 + p(2p−1), every p, once refuter-checked. The round-by-round potential is closed for p ≤ 5 but not from p = 6 (21,324 violations up to p = 8), confirming that only the stretch-level step is monotone. The ideator also proposes AM+X (one exception to always-max) for the parity-forced wins, the remaining floor of T1 (debts 2..p), and the full game at moderate heights (backlog B25–B27).
- **Refuter.** L13 and L14, proof mode: both SURVIVE, with wording fixes (V defined, |O| even, the tie rule, the induction made explicit; L14's statement made precise); both now `paper proof`. L15 and L16: proof mode running.
- **Literature.** Ideator and refuter: nothing on catch-up-order picking games; round-robin picking (fixed order, envy-free up to one item) is the closest known setting.
- **Metric.** A7: unchanged until L15's verdict (paper proofs of TI for p ≤ 2); if L15 survives: every p for a > 1 + p(2p−1).
- **Meaning.** The key idea is to stop measuring after every round: while Z has an unmatched double, Y can lower Φ temporarily, but each of Y's doubles pays at least the gaps Z's closes used, so a whole stretch never loses. Always taking the largest number is a provable drawing strategy for high pair sets.

### 2026-10-26: one exception to always-max wins the forced cases (A7)

- **Claim / question.** B25: does AM+X (always-max, except as second picker: if taking the largest number m would leave no half-taken pair and a tie with the opponent to move again, take the high of the highest other intact pair) meet every T2 target in both roles, the parity-forced wins included, and keep margin ≥ 0 as leader by any l ≥ 1 (so no pair set wins at debt ≥ 1)?
- **Approach.** `solver/src/bin/max_strategy.rs` gains the variant `amx` (per-set memo, since the exception depends on the pairing): `max_strategy 24 10 amx` (8 min; output `scratch/max_strategy-24-10-amx.md`). Regression: `max_strategy 22 8 max` reproduces `scratch/max_strategy-22-8.md` exactly.
- **Outcome.** Every target met on all pair sets within {0..23} (p ≤ 12), leads ≤ 10: margin 1 as mover at debt 0 for p odd (the win), 1 as leader by 1 for p even (the win), and as leader by l ≥ 1 the least margin is 0 or 1 by parity until l > p, then l − p.
- **Refuter.** Not run (to run with the proof, after L15's verdict).
- **Literature.** Not searched.
- **Metric.** A7: unchanged (pending L15).
- **Meaning.** One local exception turns always-max into an optimal strategy for every pair set at debts 0 and 1 and as leader, which would give all of T2 and "no pair set wins at debt ≥ 1"; with U0 that leaves only T1's floor (B26). The exception trades the basic round (−1) for a cross (0), which fits L15's proof with a two-level invariant.

### 2026-10-26: avoiding exact ties gives every row of high blocks (A7)

- **Claim / question.** B26: which simple strategy keeps the trailer's draw on {0..2p−1} at debts 2..p, where always-max fails at d = p? And does one rule give all of T1 (every debt, both roles) and T2?
- **Approach.** `scratch/b20/floor.py 7`: on intervals at debts d ≤ p (d ≡ p), play the maximum whenever it keeps the value ≥ D and list where it does not. `scratch/b20/floorrule.py 7` and `amt.py 14`: least margin of candidate one-exception rules against a perfect opponent. Then `solver/src/bin/max_strategy.rs` gains the rule `amt` and a report of the intervals at every debt d ≤ p + 1 in both roles against t_p: `max_strategy 24 12 amt` (59 s; output `scratch/max_strategy-24-12-amt.md`).
- **Outcome.** Up to p = 7 only one reachable node needs a non-maximal pick: {0,2,3,4} at debt 1 after the opponent takes 4, where the maximum 3 gives an exact tie (the opponent keeps the move) and 2 is right. Rule AM+T: always take the largest number, except as second picker when it would give an exact tie: then take the second largest. AM+T meets t_p on every interval {0..2p−1}, p ≤ 12, at every debt d ≤ p + 1 in both roles, and every T2 target (both roles at debts 0, 1, the wins included, margin ≥ 0 as leader by 1..12) on all 28,657 pair sets containing 0 within {0..23}. Failing rules: always-max (misses d = p as trailer and, for intervals, the leader's L rows), AM+X (misses d = p), "low of the top intact pair", "high of the highest other intact pair".
- **Refuter.** Not run (to run with a proof).
- **Literature.** Not searched.
- **Metric.** A7: unchanged (pending L15). If AM+T is proved: T1 for every p and d (L17), hence TI for a > 1 + p(2p−1) from both roles and the full rows.
- **Meaning.** One rule a person can play, "take the largest, but never let an exact tie hand the opponent the move", is optimal on every row of high blocks and on pair sets at debts 0 and 1. It supersedes AM+X (B25) and turns B26 into one proof target.

### 2026-10-26: the always-max lemma survives proof mode; high pair sets draw on paper (A7)

- **Claim / question.** Do the paper proofs of L15 (always-max ends ≥ −1 on pair sets) and L16 (pair sets placed above their sum draw at g0, hence TI for blocks with a > 1 + p(2p−1)) survive the refuter in proof mode?
- **Approach.** Refuter, proof mode, on the blueprint sections of 2026-10-26 (a paper proof of the always-max lemma). It audited every step and checked the induction from every balanced state that meets its hypotheses, not only reachable ones, with its own code (`scratch/refuter/l15/`). I applied its wording fixes.
- **Outcome.** L15 and L16 move to `paper proof`. Fixes adopted: the proof is a joint induction (Φ ≥ −1, and Y moves with s ≥ 1 at balanced starts with remainders), with all three routes into such starts argued (the refuter supplied the first, I added the other two); u ≥ 0 throughout a stretch follows from the first round's shape; Z's closes are assigned to j = (Y's doubles so far) + 1; final margin and l = 0 are defined; L16's parity is exact because the rounds game takes all numbers.
- **Refuter.** Proof mode (2026-10-26): L15 SURVIVES, L16 SURVIVES. Checks: every path within {0..13} (270M paths from 221k starts) and memoized within {0..17} (3.3M starts); Facts A–C, the ten one-round classes, the counting identity, the order of doubles and the close assignment all hold; the stretch bound is tight. A mutation test (Φ = −2 allowed, or Z moving at x-and-w starts) gives violations, so the checker is not vacuous. L16: always-max on all 4,181 pair sets containing 0 within {0..19} (least margin −1); a literal `valueAux` port draws all 232 pair sets within {0..11} at a = sum(E) + 2 and sum(E) + 1 + g0.
- **Literature.** Refuter: nothing on greedy strategies in Catch-Up or catch-up-order picking games (two unrelated papers opened: LIPIcs FUN 2026 paper 8, arXiv 2512.16722).
- **Metric.** A7 moved: paper proofs of TI for p ≤ 2 at every a (L7, L11), and now for every p at a > 1 + p(2p−1) (L16). Not formalized.
- **Meaning.** Even blocks high above their own size draw, for every block size, with an explicit drawing strategy for both players (take the largest number). What remains of A7 is the descent from these heights to a = 1, blocked by O9.

### 2026-10-26: a catch-up potential for AM+T (A7)

- **Claim / question.** B26: what quantity does AM+T's guarantee track, so that T1's floor (the trailer on {0..2p−1} at debts 2..p) can be proved?
- **Approach.** Scratch scripts in `scratch/b20/`: `amtreach.py`, `amtreach2.py` (reachable states from interval starts), `amtgap.py`, `amtpsi.py`, `amtfit.py` (Φ plus credits for intact pairs: no clean fit), `amtctd.py` (guarantee against the top-down alternating sum c_td), `gammastep.py 10`, `gammaall.py`, `gammacond.py`, `k2class.py`, `k3fix.py`, `gammastep_check.py 13 16` (one-round behaviour of the potential on all small sets), `amtdev.py`.
- **Outcome.** (1) The only orphan-free states with Z behind by ≥ 2 reachable from interval starts are intervals. (2) After any first-round reply Z's guarantee is exactly 0 at draw-parity debts: no slack. (3) With c = c_td(T), the potential Γ = min(s + c, 0) when Z moves, max(s − c, 0) when Y moves, never drops along AM+T play from intervals except once by 1 in a last round (p ≤ 10). (4) One round, all sets (L18, paper proof drafted, exact on all 139,230 states within {0..12}): Z's moves never lower Γ; Y's moves lower it exactly when Y moves with s < (t1 − t2) − c_td(T minus its top two). A general class closed under play is messy (Z-moving thresholds are not intervals in s), so the remaining step is to show that condition along play from intervals, where Y's holes are paid for.
- **Refuter.** Not run (L18 to go with the rest of B26's proof).
- **Literature.** Not searched.
- **Metric.** A7: unchanged (B26 intermediate: one lemma of two drafted).
- **Meaning.** The trailing player under AM+T recovers up to the alternating sum c_td of what is left, never more; this replaces Φ (which cannot see a trailing start's credit) for T1. L14's per-round inequality is the core of both directions.

### 2026-10-26: where Y moves, the potential's condition holds below the top run (A7)

- **Claim / question.** B26: does L18's condition (s ≥ (t1 − t2) − c_td(T minus its top two) wherever Y moves) hold along AM+T play from the starts we need, and what invariant explains it?
- **Approach.** Scratch scripts in `scratch/b20/`: `ycond.py 7`, `zcond.py 7`, `holes.py 8`, `holes2.py 8`, `zshapes.py 7` (structure of reachable states from intervals), `invsearch.py 9 10` (closed linear invariants over all sets), `pairgamma.py 14` (pair-set starts), `toprun.py 14`, `toprun2.py 17` (pair sets with Z trailing by d ≤ the top run).
- **Outcome.** The condition holds at every reachable Y-moving state from: intervals with Z trailing by d ≤ p (p ≤ 8); pair sets at debts 0 and 1 and with Z leading (within {0..13}); and in general pair sets with Z trailing by d ≤ r, r = the number of adjacent pairs at the top, and Z leading by any l ≤ p + 1 (all 987 pair sets within {0..16}). It fails for d = r + 1. Stated as L19 (conjecture); with L18 it gives Z ≥ −1, so T1's floor (intervals: r = p) and L15's cases for AM+T come from one per-round lemma. Along play from intervals, Y-moving starts satisfy s + |T|/2 ≥ H + 2 (H = numbers missing inside the span of T), which implies the condition; but no linear hole invariant is closed over all sets, so the proof must use where the holes are.
- **Refuter.** Not run (L19 has no proof yet).
- **Literature.** Not searched.
- **Metric.** A7: unchanged (B26: the step lemma L18 drafted; L19 stated and checked).
- **Meaning.** One per-round potential lemma plus a structural lemma about Y's holes would give all rows' floors and a Lean-friendlier proof of L15's draw cases than the stretch argument. The parity-forced wins (margin ≥ 0) still need the last-round drop excluded.

### 2026-10-26: L13 formalized: high sets are the rounds game (A7)

- **Claim / question.** B28, first node: formalize L13 (paper proof, refuter-checked) in Lean.
- **Approach.** New module `lean/CatchUp/Rounds.lean`: the rounds game `roundsValue` (recursion on the offsets, two picks per call, termination by card); `Outcome.best_congr` (best depends only on membership, from L6); `valueAux_answer` (the other player's node, including the early-loss rule); `valueAux_map_add` (L13) by strong induction on card with s universally quantified. Skeleton with `sorry` first, then four compile rounds. Imported in `CatchUp.lean`.
- **Outcome.** `CatchUp.valueAux_map_add`: for `Even O.card` and `d + ∑ O < a`, `valueAux (O.map (addLeftEmbedding a)) s (s + d) false = roundsValue O d` for every s. `lake build --wfail` clean; `#print axioms`: propext, Classical.choice, Quot.sound. Deviations from the paper proof (listed in L13's section and under Awaiting review): odd O gets a convention in `roundsValue` (mover wins without an answer; never used); s stays quantified instead of "V depends only on the deficit"; the early-loss rule is handled at the other player's node.
- **Refuter.** Not run on the Lean proof (the kernel checked it; L13's paper proof survived proof mode earlier today).
- **Literature.** Not searched.
- **Metric.** A7: unchanged (TI's paper proofs); first formalized node of the high-block route.
- **Meaning.** Results about the rounds game now transfer to the real game in Lean. Formalizing L15 (or L18 with L19) and L16 would make "high blocks draw" a checked result.

### 2026-10-26: L14 formalized: the greedy bound and both per-round inequalities (A7)

- **Claim / question.** B28: formalize L14 (paper proof, refuter-checked), whose per-round inequality L18 also uses.
- **Approach.** New module `lean/CatchUp/AltSum.lean`: `altSum` (recursion removing the maximum), the joint lemma `altSum_add_erase` (x ≤ altSum U + altSum (U − x) ≤ 2·max U − x), `altSum_round`, `altSum_top_two`, the game value `greedyWorst` and `neg_altSum_le_greedyWorst` (L14). Imported in `CatchUp.lean`; imports Mathlib's `Finset.max'`, abs, linarith and ring.
- **Outcome.** Compiled on the first full attempt apart from imports and deprecated rewrites. `lake build --wfail` clean; `#print axioms` of the three main theorems: propext, Classical.choice, Quot.sound. Deviation: the per-round inequality goes through the joint lemma instead of the paper's sign bookkeeping, and comes out two-sided (`|altSum T − altSum T'| ≤ t1 − j`), which is also L18's part (a).
- **Refuter.** Not run on the Lean proof (kernel-checked). L18's paper proof is with the refuter in proof mode.
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** The alternating-sum machinery for the per-round route to L16 (L18 with L19) is in Lean.

### 2026-10-26: Lean: the rounds game's value is the sign of its minimax margin (A7)

- **Claim / question.** B28 infrastructure: strategy arguments (L15, L18) bound final margins, while `roundsValue` scores only win, draw or loss. Can a margin bound be turned into a value bound in Lean?
- **Approach.** New module `lean/CatchUp/Margin.lean`: `Outcome.ofMargin`, the minimax margin `roundsMargin` (same recursion as `roundsValue`, `sup'` for best and minus for `neg`), `Outcome.best_eq_ofMargin_sup'`, `roundsValue_eq_ofMargin` (strong induction, through the other player's answers), and `even_roundsMargin_add` (parity). `Rounds.lean` and `AltSum.lean` now `@[expose]` their definitions so later modules can unfold them (no statement changed).
- **Outcome.** For even O: `roundsValue O d = Outcome.ofMargin (roundsMargin O d)` and `roundsMargin O d + d + ∑ O` is even. `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound. So "a strategy keeps the margin ≥ −1" plus parity gives "≥ draw" in Lean, by an induction on `roundsMargin` that picks the strategy's move at each step.
- **Refuter.** Not run (kernel-checked; standard fact: the minimax of a monotone payoff is the payoff of the minimax).
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** The Lean route to L16 needs only the strategy induction (L18 with L19) on top of these two theorems and L13.

### 2026-10-26: the potential step survives proof mode (A7)

- **Claim / question.** Does L18's paper proof (the catch-up potential step) survive the refuter in proof mode?
- **Approach.** Refuter, proof mode, with its own literal move generator (`scratch/refuter/l18/`). I applied its fixes to the statement and proof.
- **Outcome.** L18 moves to `paper proof`. Fixes: Uses L13, L14; the statement unifies the last round (c'' = 0), states the drop's size and that only Y's pick t1 causes it, and defines exact tie and second largest; part (a) is the other direction from L14 (s + c, not s − c); the exception needs \|T\| ≥ 4; the converse uses c'' > 0. A false evidence sentence corrected: with d = p + 1 a drop can also come at \|T\| = 4 (outside L19's range); at most one drop of 1 per line still holds for all starts with p ≤ 9. Plain always-max satisfies L18 as well.
- **Refuter.** Proof mode (2026-10-26): SURVIVES. 671,662 states (every even T ⊆ {0..13}, debts ≤ 40) and 6.26M random states near the thresholds, 0 mismatches; threshold mutations ±1 detected.
- **Literature.** Refuter: nothing on greedy or alternating-sum analyses of Catch-Up or of "player behind moves next" picking games.
- **Metric.** A7: unchanged (B26: L18 paper proof; L19 open).
- **Meaning.** The per-round half of the route to every row's floor, and to a Lean proof of L16, is checked; L19 is the remaining gap.

### 2026-10-26: Lean: the catch-up potential guarantee (A7)

- **Claim / question.** Formalize L18 (paper proof since today) in the form its use needs: Z's margin is at least Γ − 1 along any class of states where the condition holds.
- **Approach.** `lean/CatchUp/Potential.lean`: AM+T's answer `amtReply`; `altSum_nonneg`, `altSum_le_max'`; two bounds on `roundsMargin` from one pick or one answer per pick (`neg_le_roundsMargin`, `roundsMargin_le_neg`); `potential_le_roundsMargin`, a joint strong induction over both movers, the case split of L18's proof (Z moves; Y takes another number; Y takes t1 with an exact tie, without, and at the last round).
- **Outcome.** `potential_le_roundsMargin` proved; `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound. L18 → `formalized` (guarantee form; deviations in its section). `max'_erase_of_ne`, `erase_nonempty_of_even` made public.
- **Refuter.** Not run (kernel-checked; L18's proof survived proof mode earlier today).
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** With L19 as the closed class (Z trailing by at most the top run), every row's floor in Lean needs only L19's proof and its formal statement; L16 then needs parity (`even_roundsMargin_add`) and L13.

### 2026-10-26: ideator on A7's descent: avoid carries instead of analysing them (A7)

- **Claim / question.** How to lower the height bound of L16 (B27) and approach the descent past O9? (ideator, called at the previous review)
- **Approach.** Ideator with its own real-game and rounds-game engines (`scratch/ideator/a7/`, standalone Rust); its engine reproduces the refuter's always-max thresholds a = 1, 2, 7, 12, 21, 30 for p = 1..6.
- **Outcome.** Unchecked scratch data. (1) "Hyb": Z plays always-max until Y, as round mover, trails by more than c(R) (U0's matching cost of the numbers left), then answers each pick with its U0 partner. Sketch: Z's round-start debts stay ≤ max(g, m), Y's ≤ 3m (m the largest offset), so for a > 3m the real game equals the rounds game along every play against Hyb, and L15 + U0 give ≥ draw: blocks at a ≥ 6p − 2 instead of a > 1 + p(2p−1). Data: Hyb keeps AM's margins and AM+T's rows with max debt 4p − 4 (p ≤ 10); real game draws B(a, p) at g0 in both roles for a ≥ 4p − 6 (p = 3..8); all 1,597 pair sets with 0 within {0..17} draw at a = 3·span + 1..3. (2) "Hyb2" (take the smallest answer that leaves Y lost by U0, else AM): draws blocks in the real game exactly from a = 2p − 1 (p = 3..8); below, the last pair goes to Y in one turn. A real-game U0 is false just above the span (a = 10, R = {10, 11, 12, 17}, mover trailing by 6 wins). (3) Restricted defender games: never more than 2 picks per own turn (R1), or opponent always left under 2·min(left) behind (R2): the defender still draws {1..N} for every even-total N ≤ 24 and blocks p ≤ 7, a ≤ 40 (R2: except {2,3,4,5} and {1..6} at g0). Dropped: fixed lead caps (fail from N = 7), capped-max (loses from N = 4), same-part composition of strategies (fails on {1..2k} ∪ block for k ≥ 2).
- **Refuter.** Not run yet (B29 sends Hyb's proof in proof mode).
- **Literature.** Ideator, web: only the README's known sources; fair-division picking sequences are not this game.
- **Metric.** A7: unchanged (ideas only).
- **Meaning.** Hyb would make A7's height linear in p with a short argument on top of L13, L15 and U0; R2 is a strategy class that looks the same from a = 1 up, the kind of handle the descent lacks.

### 2026-10-26: high pair sets at linear height, on paper (A7)

- **Claim / question.** Does Hyb (B29) give TI for pair sets at a > 3m (blocks at a ≥ 6p − 2)?
- **Approach.** Wrote U0 as node L20 (matching bound) and Hyb's argument as L21: (a) round-start debts ≤ max(g, 2m) + m along every play against Hyb; (b) L13's correspondence read one round at a time needs only the round's start debt < a and max E < a; (c) a play that never switches is an always-max play (L15), one that switches is lost by Y (L20); (d) parity as in L16.
- **Outcome.** L20, L21 stated with paper proofs, status `conjecture` until the refuter's verdict.
- **Refuter.** Proof mode on L20 and L21 running (`scratch/refuter/l21/`).
- **Literature.** Not searched.
- **Metric.** A7: unchanged until the verdict (would become: every p at a > min(1 + p(2p−1), 3(2p−1))).
- **Meaning.** If it survives, A7's height bound becomes linear in p, and the transfer argument (debts bounded along one strategy's plays) is reusable for lower heights (B30).

### 2026-10-26: the lead regime R2 holds, but no simple rule inside it (A2, B31)

- **Claim / question.** B31: does a defender restricted to R2 (opponent left < 2·min(left) behind, ≤ 3 picks per own turn) still draw beyond the ideator's range, and does a simple turn rule inside R2 draw?
- **Approach.** New experiment `solver/src/bin/lead_regime.rs` (restricted D, perfect opponent; unrestricted it matches `Solver` on 312 sets). Intervals N ≤ 24, blocks p ≤ 9 at a ≤ 40, the ideator's cap variants, and five fixed turn rules inside R2.
- **Outcome.** [results/lead-regime-r2.md](results/lead-regime-r2.md). R2 draws {1..N} as player 1 and 2 for every even-total N ≤ 24, and every block p ≤ 9, a ≤ 40 at g0 in both roles except {2,3,4,5} and {1..6} (new: p = 8, 9). The cap variants reproduce the ideator's boundaries. All five fixed rules (least lead, greatest lead, largest pick, least taken, fewest picks) lose at N = 3 or 4.
- **Refuter.** Not run (data, matches the ideator's independent engine on the overlap).
- **Literature.** Not searched.
- **Metric.** A2 (shelved): unchanged; R2 is a class that holds the whole game for N ≤ 24 but is defined through values, not by an explicit rule.
- **Meaning.** Bounded turns are compatible with drawing at every height tested, but which allowed turn draws is no simple key, as for unrestricted play (A3's rules lose at N = 4). R2 does not revive A2 or A3 by itself; it narrows the strategy space a proof would need to describe.

### 2026-10-26: high pair sets draw at linear height: L20, L21 survive proof mode (A7)

- **Claim / question.** Do the paper proofs of L20 (matching bound) and L21 (TI for pair sets at a > 3m via Hyb) survive the refuter in proof mode?
- **Approach.** Refuter, proof mode, with its own rounds-game engines and a literal `valueAux` port (`scratch/refuter/l21/`). I applied its fixes.
- **Outcome.** Both SURVIVE → `paper proof`. Fixes: the per-round transfer, used by L21 (b), is its own node L22 (strategy transfer; `valueAux_map_add` needs d + sum(O) < a and does not apply at a = 3m + 1); Hyb in the real game numbers picks from the start, picks 2k − 1 and 2k forming round k; "same outcome" instead of "same final margin" (early-loss endings leave a number untaken); L20 uses no lemma; L21 needs p ≥ 1; the largest round-start debt against Hyb on blocks is 4p − 5 = 2m − 3, not 4p − 4.
- **Refuter.** Proof mode (2026-10-26): SURVIVES. L20 tight on every even O ⊆ {0..9}; (a)'s bounds on all 4,181 pair sets within {0..19} and all even sets within {0..14}; per-node rounds/real agreement on 650,774 nodes; Hyb draws all 610 pair sets within {0..15} at a = 3m − 2..3m + 1; mutation detected.
- **Literature.** Refuter: nothing new on matching or pairing strategies for Catch-Up.
- **Metric.** A7 moved: TI on paper for every p at a ≥ 6p − 2 (L21), besides a > 1 + p(2p−1) (L16) and p ≤ 2.
- **Meaning.** The height bound is linear. The method (bound the debts along one strategy's plays, then L22) applies to any strategy with a debt bound; Hyb's measured bound 2m − 3 and Hyb2's (B30) suggest a ≥ 2p − 1 is in reach.

### 2026-10-26: a depth-weighted invariant gives the draw entries of high-block rows (A7)

- **Claim / question.** How to prove L19, or reach T1's floor (Z trailing by d ≤ p on {0..2p−1} secures margin ≥ −1) another way? (ideator, called at unit 11)
- **Approach.** Ideator: finite closed-class searches over (T, s) for invariants of AM+T play (`scratch/ideator/l19/`). I wrote its sketch out as node L23 and checked each case by hand.
- **Outcome.** L23 (conjecture, paper proof written): the class K (s + q ≥ D_Z(T) when Z moves, s + q ≥ D_Y(T) and s ≥ 1 with holes when Y moves, holes weighted by their depth below t2 or t1, explicit last round) is closed under every AM+T round. Intervals have no holes, so both players' AM+T guarantees give R({0..2p−1}, d) = draw for every d ≤ p with d ≡ p (L17's draw entries); L20 gives the losses for d > p. It bypasses L18 + L19 for intervals; L19 stays open for spaced pair sets. Data (ideator, unchecked): closure on 272,103 K-states within {0..13} and 113,972 with independent code within {0..11}, 184k random boundary states, each weakening breaks closure; plain always-max fails closure only at Y-moving ties. Other ideas: debts along AM+T plays (Z's ≤ p, Z's lead ≤ p² + p) would transfer the draw entries to blocks at a > p² + p by L22; an odd-parity analogue of K for the forced ±1 entries (four template families failed); a hybrid of K and L15's credits for spaced pair sets; K-like depth weights as an A2 class on {1..N}.
- **Refuter.** Proof mode on L23 running (`scratch/refuter/l23/`).
- **Literature.** Ideator: nothing using this rule or a hole-depth potential (picking-sequence work only).
- **Metric.** A7: unchanged until the verdict.
- **Meaning.** A per-round invariant with explicit sums is the Lean-friendly route to TI for blocks and to L17's draw entries; only the parity-forced entries of t_p would remain open.

### 2026-10-26: Lean: the matching bound (A7)

- **Claim / question.** Formalize L20 (paper proof since today).
- **Approach.** `lean/CatchUp/Matching.lean`: `matchCost` (two smallest, then recurse), `matchCost_of_min` (unfolding at the two smallest), `matchCost_nonneg`, `exists_partner` (every i has a j with c(O − {i, j}) + \|i − j\| ≤ c(O)), `roundsMargin_le_matchCost` by strong induction with `roundsMargin_le_neg`. Drafted in scratch while the refuter ran, moved in after the verdict.
- **Outcome.** L20 → `formalized`; `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound. Deviation (in its section): the answer is given by `exists_partner` rather than named.
- **Refuter.** Not run (kernel-checked; L20 survived proof mode today).
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** The loss half of L17's rows (d > p) and the switch half of L21 are checked; a checked L21 or L16 still needs L22 in Lean and L15 or L23.

### 2026-10-26: the frugal switch keeps the opponent from double picks at a ≥ 2p − 1 (A7)

- **Claim / question.** B30: along Hyb2 play on blocks, how far behind does Y get, and does the real game ever allow Y a two-pick turn at a ≥ 2p − 1?
- **Approach.** New experiment `solver/src/bin/hyb2_states.rs` (real game, Z on a rule, Y perfect; rounds-game reach; height thresholds). It reproduces always-max's thresholds 1, 2, 7, 12, 21, 30 (refuter), Hyb's 4p − 6 (ideator) and Hyb's largest round-start debt 4p − 5 (refuter). `scratch/b20/hyb2_closure.py` tests a candidate invariant, `hyb2_trace.py` finds lines reaching the bound.
- **Outcome.** Under Hyb2, Y's round-start debt minus the smallest offset left is ≤ 2p − 1 (equality for p ≥ 3, p ≤ 9), Z's ≤ 1. So for a ≥ 2p − 1 every pick by a round mover catches up, and (with L22's proof, which needs only that) the real game against Hyb2 is the rounds game; Hyb2 guarantees ≥ draw there (L15 before the switch, L20's invariant after). Real game, p ≤ 8, a ∈ [2p − 1, 4p]: no Y round start allows a double pick, Z secures ≥ 0 in both roles. Hyb2 draws exactly from a = 2p − 1. The debt bound is not closed over arbitrary states (R = {0,1,2,3}, e = 3). Written as L24 (conjecture; open step: the debt bound).
- **Refuter.** Not run (conjecture; the proof of its open step goes to an ideator first).
- **Literature.** Not searched.
- **Metric.** A7: unchanged (L24 conjecture).
- **Meaning.** One lemma (Hyb2's debt bound) separates A7 from TI at every doubling-free height; below a = 2p − 1 double picks are unavoidable for this strategy.

### 2026-10-26: Lean: strategy transfer from the rounds game to the real game (A7)

- **Claim / question.** Formalize L22 (paper proof since today), the step every high-block result shares.
- **Approach.** `lean/CatchUp/Transfer.lean`: helpers for `best` (`best_ne_win`, `best_ne_loss`), `neg`, `valueAux_step` (one unfolding outside the opening), list membership on translated offsets; `valueAux_transfer` by strong induction over the set left, unfolding the mover's node and the answerer's node, with the early-loss rule ruled out at round starts (one pick covers the debt) and at Z's answer node (Z's answer catches up, or two numbers are left).
- **Outcome.** L22 → `formalized` in invariant-class form with the draw threshold; it needs only debt ≤ a + min R at round starts, which is the form L24 uses. `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound. Deviations in L22's section.
- **Refuter.** Not run (kernel-checked; L22 survived proof mode as L21 (b)).
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** A checked TI for high blocks now needs, in Lean, only a strategy class with a debt bound and a margin guarantee: L23 (once verified) plus a debt bound (B32), or L15, or L24 (a).

### 2026-10-26: the depth class does not transplant to low sets (A2, B34)

- **Claim / question.** B34: can L23's class, deficit ≤ q − D_Z(numbers left), serve as the defender's class on {1..N} (A2's revival)?
- **Approach.** `scratch/b20/b34_first_turn.py`: player 2's first turn start after each opening x on {1..N}, every even-total N ≤ 20, q = half the numbers left (floor and ceiling).
- **Outcome.** Every opening x ≥ 2 puts player 2 outside the class already at its first turn (deficit x against q − D_Z ≤ q ≈ N/2; e.g. N = 20, x = 19, D_Z = 0, q = 9). Recorded as O11; B34 removed.
- **Refuter.** Not run (a direct count).
- **Literature.** Not searched.
- **Metric.** A2 (shelved): unchanged.
- **Meaning.** In the rounds game deficits are offsets below the round's pick size; at height 1 they are raw numbers. A depth class for the real game would need a deficit measured against the numbers left (e.g. relative to min or 2·min, as R2 does), not this literal one.

### 2026-10-26: the depth invariant survives proof mode (A7)

- **Claim / question.** Does L23's paper proof (the depth invariant K for AM+T) survive the refuter in proof mode?
- **Approach.** Refuter, proof mode, own code written without the ideator's (`scratch/refuter/l23/`). I applied its fixes.
- **Outcome.** L23 SURVIVES → `paper proof`. Fixes: the consequence is only the draw entries of t_p (L17 stays a conjecture; its section now lists what is proved and what is open); KZ/KY named in the statement; the start's mover at s = 0 is the given one; (B) and (C) need q ≥ 2, (B)'s last case reworded; three unstated last steps written out; (E) renamed (D); Uses L13; the ideator's "(9 cases)" replaced by the refuter's count.
- **Refuter.** Proof mode (2026-10-26): SURVIVES. Closure on 1,000,627 K-states within {0..15} and 3,856,947 within {0..16}; Z's guarantee ≥ −1 from all 987,901 K-states within {0..15} against a perfect Y; every intermediate claim of every case; 1,016,606 random boundary states; every mutation breaks closure. Exact minimax matches t_p for p ≤ 8, d ≤ p + 3.
- **Literature.** Refuter: OEIS A278587 opened (values only); nothing on rounds games or hole-depth invariants.
- **Metric.** A7: unchanged (TI's range stays a ≥ 6p − 2; L23 adds the rows' draw entries at heights where L13 applies).
- **Meaning.** The draw entries of every high block's row now have a refuter-checked per-round proof, the form that suits Lean: with L13 or L22 and parity it gives TI in Lean once K is formalized.

### 2026-10-26: Lean: the depth invariant, and high blocks draw (A7)

- **Claim / question.** Formalize L23 (paper proof since today) and with it TI for high blocks.
- **Approach.** `lean/CatchUp/Depth.lean`: holes and depths as Finset sums, the one-step decomposition when the top is removed, the three removal lemmas behind (B), a lower bound on gap sums; the classes in debt form; `closeZ` and `closeY` follow the paper's cases, each ending in one `omega` over the decomposition facts (products such as m·b1 enter as atoms with their bounds); `depth_class_roundsMargin` by strong induction with `neg_le_roundsMargin` / `roundsMargin_le_neg` and `amtReply`. `lean/CatchUp/Blocks.lean`: intervals have no holes, parity gives margin 0, `roundsValue_eq_ofMargin` and L13 give the real game.
- **Outcome.** L23 → `formalized`. `CatchUp.block_draw_high`: for every p ≥ 1 and a > p mod 2 + p(2p−1), V({a..a+2p−1}, p mod 2) = draw, Lean-checked (`lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound). This is the block case of L16; L16 stays `paper proof` for general pair sets. Deviations in L16's and L23's sections.
- **Refuter.** Not run (kernel-checked; L23 survived proof mode today).
- **Literature.** Not searched.
- **Metric.** A7: paper range unchanged (a ≥ 6p − 2 via L21); new: TI is Lean-checked for every p at a > p mod 2 + p(2p−1).
- **Meaning.** The first infinite family of Catch-Up draws checked in Lean here. Not a solution of the problem (it says nothing about {1..N}); reporting it needs your approval of its statement.

### 2026-10-26: Lean: high blocks draw at linear height (A7)

- **Claim / question.** Formalize L21 for blocks: V({a..a+2p−1}, p mod 2) = draw for a ≥ 6p − 2.
- **Approach.** `lean/CatchUp/Linear.lean`: Hyb with AM+T before the switch. Classes `HZ`, `HY`: subsets of {0..2p−1}, even size, parity of debt plus the numbers left; before the switch L23's `KZc`/`KYc` with debts ≤ 2p − 1 (Z) and ≤ 2(2p − 1) (Y); after it Y's debt above the matching cost with debt + cost ≤ 3(2p − 1). `hz_step` from `closeZ`, `hy_step` from `closeY` before the switch and `exists_partner` (L20) after; `matchCost_le_span` bounds the cost by the span; `valueAux_transfer` (L22) carries both guarantees to the real game.
- **Outcome.** `CatchUp.block_draw_linear`: for every p ≥ 1 and a > 3(2p − 1), the block {a..a+2p−1} is a draw for the player to move trailing by p mod 2. Lean-checked (`lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound). Deviations in L21's section. L21 stays `paper proof` (general pair sets).
- **Refuter.** Not run (kernel-checked; L21 and L23 survived proof mode).
- **Literature.** Not searched.
- **Metric.** A7: the Lean-checked range of TI drops from quadratic height (a > p mod 2 + p(2p−1)) to linear, a ≥ 6p − 2, matching the paper range.
- **Meaning.** Every block draw proved on paper so far is now checked in Lean. Lower heights need a smaller debt bound (L24, B29's 2m − 3) or a new class; {1..N} itself is at height 1.

### 2026-10-26: ideas beyond high blocks: a two-ended defender (A3, A7)

- **Claim / question.** Ideator at the review after unit 22, beyond high blocks: is there a real-game analogue of the high-block guarantee, a defender whose guarantee a per-turn potential tracks, and what do results/ and the solver say?
- **Approach.** `ideator` (effort max), own scratch code in `scratch/ideator/review2/` (menu games with restricted defenders up to N = 28, block menus, deque model, rollouts), Python cross-checks `check_sm.py`, `check_block.py`.
- **Outcome.** No always-max-type defender works at a = 1: always-max, AM+T, top-k menus, rollouts and "max first, then perfect" lose on {1..N} by margins growing with N (−8 at N = 16); a Γ-type bound fails on general sets (O7's core). Kept: B35 two-ended defender (3 smallest or 3 largest, optimal among them) draws {1..N} for N ≤ 28 in both roles and blocks p ≤ 8, a ≤ 80; B36 deque toy model (TI for p ≤ 12, a ≤ 60); B37 margin domination on blocks (p ≤ 7, a ≤ 50, one-sided, survives O9). All unchecked.
- **Refuter.** Not run (ideas with unchecked data; each test is in its backlog item).
- **Literature.** Ideator: searches on Catch-Up proofs, catch-up-order picking and sequential allocation; plus.maths.org (2022) has nothing beyond the 2015 computations; nothing on end-restricted variants.
- **Metric.** None moved (A3 shelved: 4; A7 unchanged).
- **Meaning.** At low heights the defender's play is at the bottom of the set, which top-down potentials (L18's Γ, L23) cannot see; a two-regime strategy (bottom at low heights, top at high ones) is the candidate. If B35's side rule exists, A3 revives with two potentials.

### 2026-10-26: Lean: every draw entry of high-block rows at linear height (A7, B26)

- **Claim / question.** Does the Lean proof of `block_draw_linear` give every draw entry of the row, V({a..a+2p−1}, d) = draw for d ≤ p, d ≡ p (mod 2), not only d = p mod 2?
- **Approach.** `lean/CatchUp/Linear.lean`: `block_row_draw_linear` with the start debt d as a parameter. Z moving: `kzc_range` needs d ≤ p. Z as the other player: d ≤ c(R) puts the start in `HY`'s first branch (L23's `kyc_range`), else the second (d + c(R) ≤ p + 2p − 1 ≤ 3(2p − 1)). Parity: d + p(2p − 1) even. `block_draw_linear` is now its case d = p mod 2 (statement unchanged).
- **Outcome.** `CatchUp.block_row_draw_linear` Lean-checked (`lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound): the draw entries of L17's rows hold for blocks at a ≥ 6p − 2. L17 stays a conjecture (parity-forced entries, B33).
- **Refuter.** Not run (kernel-checked; the refuter's statement check of `block_draw_linear` found debt p mod 2 + 2 also drawing in its rows, consistent).
- **Literature.** Not searched.
- **Metric.** A7: unchanged (TI's range); L17's draw entries now Lean-checked at a ≥ 6p − 2.
- **Meaning.** The whole draw band [0, p] of the high-block row is checked, the band A7's kill criterion watches; what is left of the rows is the parity-forced entries.

### 2026-10-26: statement audit of block_draw_linear (A7)

- **Claim / question.** Does `CatchUp.block_draw_linear` say what we mean ("the block {a..a+2p−1} with a ≥ 6p − 2 is a draw for the player to move trailing by p mod 2")?
- **Approach.** `audit-statement`: read-back, trap checklist, tests in `lean/CatchUp/Tests/BlockDrawLinear.lean` (set equality, `value` form for p even, the debt's parity cannot be dropped, p = 0, implies `block_draw_high` for p ≥ 3), solver `block_rows 8 80` (every block p ≤ 8, a ≤ 80 draws at debt p mod 2), refuter in statement mode.
- **Outcome.** No gap between the Lean and the informal version. Applied the refuter's fixes: state.md said `block_draw_high` is implied (only for p ≥ 3); the doc's "at any scores" now says "from any common base score". Audit under Awaiting review; not approved (the user approves).
- **Refuter.** Statement mode (2026-10-26): SAYS WHAT WE MEAN. Independent Python port of `valueAux` (reproduces OEIS A278587 for N = 3..13): all cases p ≤ 4, a = 6p−2..6p+3, s ∈ {0, 1, 7}, both opening flags, draw; non-degenerate (losing first picks exist); the solver hazard is not reached here.
- **Literature.** Refuter: OEIS A278587 opened; searches on Catch-Up with consecutive or translated sets found nothing beyond the README's sources.
- **Metric.** A7: unchanged.
- **Meaning.** If you approve it, the block result can be reported as a Lean-checked partial result (with a write-up first, `writeups/`).

### 2026-10-26: a potential for Hyb2's debt bound (A7, B30)

- **Claim / question.** L24 (a): along Hyb2 plays on {0..2p−1}, is every Y round-start debt ≤ 2p − 1 + min R, and why?
- **Approach.** `ideator` (effort max), scratch `scratch/ideator/l24/`: potentials checked over all states (reachable or not), mutations, reachable plays (`reach.py` reproduces `hyb2_states`' counts).
- **Outcome.** Candidate W (L24's section): never increases over a Hyb2 round on all 196,590 states with R ⊆ {0..13} and 80,000 random states of span 50, equals 2p − 1 at the start, bounds Y's debt minus min R; each mutation breaks it; a five-transition paper sketch. Z's half of (a) is not needed. Found an error in L24 (b): the formalized L22 needs offsets < a, which fails at a = 2p − 1 (top offset = a); o ≤ a suffices in its proof. Follow-ups: B38 (rows at a ≥ 2p − 1), B39 (pair sets at a ≥ 2m − 2p + 1), B41 (the one-pick floor); B28 now targets Hyb2T in Lean. Removed: B19 (answered by `block_rows 8 80`), B29 (done: L20–L22; its tighter bound is W), B32 (superseded by `block_row_draw_linear`).
- **Refuter.** Claim mode on W running.
- **Literature.** Ideator: Catch-Up proof searches (only the README's sources); matching-potential searches found game matching and greedy matching papers, nothing on this game.
- **Metric.** A7: unchanged until W survives.
- **Meaning.** If W holds, L24 needs a paper proof of W, the relaxed L22, and (c), giving TI at a ≥ 2p − 1: the doubling-free height, below which every round-based method needs double picks.

### 2026-10-26: Lean: strategy transfer with offsets up to a (A7, B30)

- **Claim / question.** Does `valueAux_transfer` (L22) hold with offsets ≤ a instead of < a, as L24 (b) needs at a = 2p − 1?
- **Approach.** Weakened the hypotheses `hZa`, `hYa` in `lean/CatchUp/Transfer.lean` to `o ≤ a ∧ d ≤ a + o`; the proof's `omega` steps went through unchanged (the strict bound only fed 2a ≥ a + i).
- **Outcome.** Builds clean (`lake build --wfail`; axioms propext, Classical.choice, Quot.sound); `block_draw_linear` and the tests unchanged. L24 (b) now holds at a ≥ 2p − 1 given (a).
- **Refuter.** Not run (kernel-checked).
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** L24 now rests only on (a) (W, refuter running) and (c).

### 2026-10-26: Lean: the matching cost as a parity count (A7, B28)

- **Claim / question.** Is L20's cost c(O) the number of points x at which an odd number of elements of O are ≤ x, and does removing i < j change it by (j − i) − 2·(odd points in [i, j))? (The first tool of W's sketch for L24 (a), and the one new fact B28's Hyb2T route needs.)
- **Approach.** `lean/CatchUp/CostParity.lean`: `OddBelow`; `matchCost_eq_card_odd` by strong induction (the odd points of O are [o₁, o₂) plus those of the rest, all at or above o₂); `matchCost_erase_two` by comparing the two parity counts point by point (`oddBelow_erase_two`: removing i < j flips the parity exactly on [i, j)).
- **Outcome.** Both kernel-checked (`lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound).
- **Refuter.** Not run (kernel-checked).
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** If W survives, its transitions become arithmetic on these two facts plus the pair structure, which suits Lean.

### 2026-10-26: two-ended menus need a growing window on blocks (A3, B35)

- **Claim / question.** B35's cheap check: does the two-ended menu tb3 (3 smallest or 3 largest left) keep drawing even blocks at p = 9, 10, heights a ∈ [p, 2p], and does tb4?
- **Approach.** New experiment `two_ended_blocks` (dense memo over (subset, gap)); reproduced the ideator's tb2 and tb3 values for p ≤ 9 first. Commands and data in [results/two-ended-blocks-p9-10.md](results/two-ended-blocks-p9-10.md).
- **Outcome.** tb3 fails as mover (margin −2) at p = 9, a = 12 and p = 10, a = 13–15; tb4 draws p = 10 at every a ∈ [10, 20]. The other role never fails.
- **Refuter.** Not run (a measurement; reproduced against the ideator's engine).
- **Literature.** Not searched.
- **Metric.** A3 (shelved): unchanged.
- **Meaning.** The needed window grows with p (tb2 fails from p = 5, tb3 from p = 9), so "two-ended" is a search-space restriction, not yet a bounded strategy; the side-rule test should be posed with windows growing with p.

### 2026-10-26: short turns suffice for blocks down to height 2 (A7, B41)

- **Claim / question.** B41: from which height can a defender draw blocks while keeping turns short? The ideator proposed "the opponent trails by at most the smallest number left" as the floor of rounds-game methods.
- **Approach.** `lead_regime` (existing engine) with caps m and 2m − 1 on the opponent's deficit after D's turn, D at most 2 or 3 picks; blocks p ≤ 9, a ≤ 40, and intervals N ≤ 24. [results/lead-regime-short-turns.md](results/lead-regime-short-turns.md).
- **Outcome.** Cap m (one-pick opponent turns) fails at every height for p ≥ 2, so the proposed test does not measure the rounds structure: under Hyb2 the opponent's turn after Z's top pick often has 2 picks, and only round starts are single-pick. Both players at most 2 picks per turn (cap 2m − 1, D ≤ 2 picks): D draws every block in both roles at every a ≥ 2 for p = 3..9 (p = 2 fails at a = 2), failing only at a = 1; on {1..N} D fails as player 2 from N = 8. With 3 picks for D (R2) all of it draws.
- **Refuter.** Not run (a measurement with a checked engine).
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** Short turns are not what stops round-based methods below a = 2p − 1: two-pick turns suffice down to a = 2. A rounds-style descent would need a bookkeeping in which a round's first mover may take two picks; at a = 1, D needs three-pick turns. Passed to the descent ideator. B41 removed (answered; the floor of strict rounds bookkeeping is not measured).

### 2026-10-26: Hyb2T keeps every draw entry of the rows to p = 9 (A7, B38)

- **Claim / question.** B38: does Hyb2T (AM+T before the switch, the smallest valid answer after it) secure at least a draw in the real game on {a..a+2p−1} at every draw entry d ≤ p, d ≡ p, both roles, from a = 2p − 1, for p = 8, 9 as for p ≤ 7?
- **Approach.** The ideator's `scratch/ideator/l24/rows.py 9` (Z on Hyb2T, Y perfect; heights 2p − 2, 2p − 1, 2p); output `scratch/b38-rows-9.txt`, 94 s.
- **Outcome.** For every p = 2..9: Z's least guarantee over the draw entries in both roles is 0 at a = 2p − 1 and 2p, and −(2p − 2) at a = 2p − 2.
- **Refuter.** Not run yet (the ideator's own code; B38's next step is claim mode with an independent engine).
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** Consistent with W: if L24 holds, the rows' draw entries come with it at a ≥ 2p − 1.

### 2026-10-26: Hyb2's debt bound on paper: node L25 (A7, B30)

- **Claim / question.** L24 (a): does the potential W never increase over a Hyb2 round, so that every Y round start has e ≤ 2p − 1 + min R and every Z round start d ≤ 2p − 1?
- **Approach.** The L24 ideator wrote out its sketch as a full paper proof (tools (A)–(F), Hyb2's answer structure P1–P3 and Q1–Q4, transitions T1–T4b, consequences), citing the two Lean facts of `CostParity.lean`; I checked every step by hand against the definitions and moved it into the blueprint as node L25.
- **Outcome.** L25 stated with its proof (status `conjecture` until the refuter's proof-mode verdict). I found no gap. Z's debt after a fallback where Y took max R is ≤ span ≤ 2p − 1; the stronger "Z's debt ≤ 1 + min R" of L24's first statement is not needed and not proved. L24 now uses L25.
- **Refuter.** Proof mode on L25 running; claim mode on W (own engine) running.
- **Literature.** Not searched (refuter will).
- **Metric.** A7: unchanged until L25 survives.
- **Meaning.** With L25, L24 (TI at a ≥ 2p − 1) has a complete paper route: L25 → L22 (offsets ≤ a, Lean) → L15 and L20 → parity.

### 2026-10-26: the potential W holds in claim mode (A7, B30)

- **Claim / question.** L25's claim: W never increases over a Hyb2 round from any start with even debt + sum, starts at 2p − 1, so Y's debt ≤ 2p − 1 + min R and Z's ≤ 2p − 1.
- **Approach.** Refuter in claim mode with its own engine (Rust, and a literal Python port that matches it exactly at U = 11); first reproduced L24's measured evidence and the ideator's state count.
- **Outcome.** HOLDS: no rise over 1.14·10⁹ round starts (all even sets of span ≤ 26, debts up to c + 20), span ≤ 21 to c + 100, sparse and random sets, every reachable start for p ≤ 13. Every mutation breaks it; the definition's sharp points (e ≥ c, ≥ in "valid", o₂ absolute, parity) are as L25 states them.
- **Refuter.** Claim mode (2026-10-26): HOLDS (tested range). Proof mode on L25 running.
- **Literature.** Refuter: Delon–Salomon–Sobolevski (arXiv 1102.1558, nested minimum matchings on the line) has no odd-count form of the cost; nothing on this potential.
- **Metric.** A7: unchanged until proof mode.
- **Meaning.** The numerical side of L24 (a) is settled to span 26; what remains is the proof-mode check of L25's argument.

### 2026-10-26: deque Catch-Up rows have two clean regimes (A7, B36)

- **Claim / question.** B36: in the deque model (every pick the smallest or largest left), can the rows of even blocks be described by a few thresholds?
- **Approach.** `scratch/b36/deque_rows.rs` (exact margins by interval and debt, DP by length); first reproduced the ideator's values: deque TI holds for p ≤ 12, a ≤ 60, and every even-total {1..N} draws for N ≤ 100. Then the draw-parity rows of [lo, lo + 2p − 1] for p ≤ 30, lo ≤ 200 as runs (`runs-200-30.txt`).
- **Outcome.** For p ≥ 3: at lo ≤ p − 1 the row is a draw at every draw-parity debt up to the top; from lo = 3p − 4 on (exactly, every lo ≤ 200) it is D for g ≤ p, L for p < g ≤ lo, W for g > lo (the mover then takes two picks and jumps ahead); p ≤ lo ≤ 3p − 5 are mixed. p = 1, 2: the pattern holds from lo = 1, 2.
- **Refuter.** Not run (toy model, scratch).
- **Literature.** Not searched.
- **Metric.** A7: unchanged.
- **Meaning.** In the toy, TI holds at every height and the high regime starts at a linear height, as in the real game; the mixed band p ≤ lo ≤ 3p − 5 is where a descent must work. A full proof would need the values of odd lengths and off-parity debts too (next step of B36).

### 2026-10-26: a two-ended defender draws {1..N} to N = 24, checked (A3, B35)

- **Claim / question.** B35's main lead, so far only the ideator's: does a defender restricted to the 3 smallest or 3 largest numbers left draw {1..N} in both roles?
- **Approach.** New experiment `two_ended_intervals` (same menu logic as `two_ended_blocks`, dense memo); tb1, tb2, tb3 for even totals N ≤ 24. [results/two-ended-intervals-n24.md](results/two-ended-intervals-n24.md).
- **Outcome.** tb3 draws every even-total N ≤ 24 in both roles. tb2 fails from N = 19 (reproducing the ideator), tb1 from N = 7.
- **Refuter.** Not run (an independent engine reproducing the ideator's tb2 threshold; the claim to N = 28 stays the ideator's).
- **Literature.** Not searched.
- **Metric.** A3 (shelved): unchanged; the lead is confirmed to N = 24.
- **Meaning.** At height 1 a defender never needs a middle number up to N = 24, while on blocks the window must grow with p (tb3 fails at p = 9, 10): {1..N} is easier for the two-ended defender than translated blocks. Next: where it must pick from the top (B35's side rule).

### 2026-10-26: Hyb2's debt bound survives proof mode (A7, B30)

- **Claim / question.** Does L25's paper proof (the potential W never rises over a Hyb2 round) survive the refuter in proof mode?
- **Approach.** Refuter, proof mode, own literal code (`scratch/refuter/l25/`).
- **Outcome.** L25 SURVIVES → `paper proof`. Two wording fixes applied (part 7). L24 now has every step on paper: (a) = L25, (b) via the formalized, relaxed L22, (c) L15 and L20, (d) parity; L24 itself still needs its own proof-mode check before it counts.
- **Refuter.** Proof mode (2026-10-26): SURVIVES; 58 step-level claims, 0 failures over all sets within {0..16} containing 0 and random sets within {0..60}; parity hypothesis shown necessary.
- **Literature.** Refuter: OEIS A278587, the von Stengel talk abstract (computation to 28, no proof); no Catch-Up proof or matching-cost potential found.
- **Metric.** A7: unchanged until L24 passes proof mode (would move the paper range to a ≥ 2p − 1).
- **Meaning.** The high-block line's last open step is closed on paper. Whether it helps {1..N} depends on whether the two-ended defender's top-pick positions are high sets (B35's side rule, next).

### 2026-10-26: blocks at a ≥ 2p − 1 draw on paper (A7, B30)

- **Claim / question.** Does L24's proof (blocks {a..a+2p−1} draw at debt p mod 2 for a ≥ 2p − 1, via Hyb2 = L25 + relaxed L22 + L15 + L20's partner step + parity) survive proof mode?
- **Approach.** Refuter, proof mode, with its own real-game port (`scratch/refuter/l24/`).
- **Outcome.** SURVIVES → L24 `paper proof`. Wording fixed: KZ, KY, `hendZ` named, offsets ≤ a, L20's partner step cited. Bound tight: Hyb2 loses at a = 2p − 2 (p ≥ 3). A Lean route that avoids L15 (AM+T before the switch, then L23's classes) is logged on L24.
- **Refuter.** Proof mode (2026-10-26): SURVIVES; real-game Hyb2 draws for p ≤ 7, a ∈ [2p − 1, 6p], both roles.
- **Literature.** Refuter: A278587, MPRA 108784 (search hit only); no result on shifted blocks.
- **Metric.** A7: paper range a ≥ 3(2p − 1) + 1 (Lean, L21) → a ≥ 2p − 1 (paper), the doubling-free height.
- **Meaning.** High blocks are settled on paper down to a ≈ 2p, half the length of the block. {1..N} is a = 1, p = N/2: the gap from 2p − 1 to 1 is the descent (O9), which the blocks method cannot cross on its own; the side rule of the two-ended defender (B35) is the next unit.

### 2026-10-26: two-pick turns for both players suffice on {1..N} to N = 24; correction (A2, B41)

- **Claim / question.** Can D draw {1..N} while every turn of both players is at most 2 picks? Corrects "2026-10-26: short turns suffice for blocks down to height 2", whose engine (`lead_regime`) refused turns that win outright, so its failures at a = 1 and on {1..N} are not established.
- **Approach.** New experiment `turn_cap` with the exact condition (opponent behind by at most the sum of its 2 smallest numbers left); independent script `scratch/turn_cap/check.py` from the rules; `lead_regime` fixed (49a7676). [results/turn-cap-intervals-n24.md](results/turn-cap-intervals-n24.md).
- **Outcome.** D draws every even-total N ≤ 24 in both roles with turns ≤ 2 picks for both players. One-pick opponent turns fail from N = 7. For N ≤ 12 the class still draws with cap 2m − 1 and with D also limited to its 3 smallest or 3 largest numbers.
- **Refuter.** Not run; outcomes reproduced by an independent script to N = 12.
- **Literature.** Not searched.
- **Metric.** A2 (shelved): a candidate class (turns ≤ 2 picks for both) holds to N = 24; its closure is not a class of positions yet.
- **Meaning.** Multi-pick turns at height 1 never need more than 2 picks, for either player, as far as computed: the low game is a "two-round" game, the next step up from the rounds game of high sets. The blocks entries of the corrected results still need the fixed `lead_regime` rerun.

### 2026-10-26: while the set is low, the defender needs only its smallest numbers (A3, B35)

- **Claim / question.** Where must the two-ended defender use the top (`two_ended_sides`)? And can it play from the bottom only until the set is high?
- **Approach.** `two_ended_sides 16 3`: along tb3's drawing play D's positions are 20% bottom-only, 1% top-only, 79% either; top-only positions are high sets (e.g. {8..15} at gaps 2, 4) and endgames. New experiment `low_high`: D picks among its k smallest while min < c·span, freely once high. [results/low-high-n24.md](results/low-high-n24.md).
- **Outcome.** For N ≤ 24: the 2 smallest suffice while max > 3·min (c = 1/2); the 4 smallest suffice until min ≥ span (c = 1, L24's high regime); the needed k grows with c (c = 1: k = 1, 2, 3 fail first at N = 7, 11, 19).
- **Refuter.** Not run; reproduced by an independent script to N = 12.
- **Literature.** Not searched.
- **Metric.** A3 (shelved): no fixed rule yet; the low phase needs only the k smallest numbers (k = 2 at c = 1/2) to N = 24.
- **Meaning.** A possible split of {1..N}: a low phase where D only makes change with its smallest numbers, and a high phase in the regime L24/L25 handle. Open: whether the needed k stays bounded as N grows, and what the positions at the switch look like (whether L25's class contains them).

### 2026-10-26: Hyb2 is not a universal high-phase strategy (A8, B35)

- **Claim / question.** A8's high phase: does Hyb2 draw from every high position where a draw is possible, or must the low phase reach a narrower class?
- **Approach.** New experiment `hyb2_universal` (rounds game, every even O ⊆ {0..15}, every debt with even parity, both roles; exact vs Hyb2 against a perfect opponent). [results/hyb2-universal-u16.md](results/hyb2-universal-u16.md). Also `scratch/a8/switch.py` (N = 12): the positions where the set first becomes high under drawing low play (bottom 4) are mostly small sets with holes (942 of them; 199 full blocks), so the low phase lasts most of the game.
- **Outcome.** Hyb2 fails to secure an available draw at about 6% of positions in each role; the smallest failures have a hole next to the bottom ({0, 2, 3, 4} at d = 1). Full blocks draw, as L24 says.
- **Refuter.** Not run (a negative search fact, checked against L24 on blocks).
- **Literature.** Not searched.
- **Metric.** A8: unchanged; H must be narrower than "high and drawable", e.g. L25's class plus a start condition, or a different high strategy.
- **Meaning.** The split works only with a described class H that the low phase can force; since the switch comes late (few numbers left), most of the difficulty sits in the low phase, not the high one.

### 2026-10-26: short turns with the cap 2m − 1, rerun with the fixed engine (A2, B41)

- **Claim / question.** Rerun of "2026-10-26: short turns suffice for blocks down to height 2" after both outright-win fixes (49a7676 missed a second cap check; 42b7716).
- **Approach.** `lead_regime` battery as before; [results/lead-regime-short-turns.md](results/lead-regime-short-turns.md) replaced.
- **Outcome.** Cap 2m − 1, D ≤ 2 picks: blocks draw for p ≤ 7 at every a ≤ 40 and for p = 8, 9 except a = 1; {1..N} draws as player 1 to 24, as player 2 only to 12. The exact cap (sum of the 2 smallest) draws everything to 24, so the difference is the cap's slack, not the turn length. One-pick opponent turns still fail almost everywhere; fixed rules still fail at N = 3–4.
- **Refuter.** Not run; intervals agree with `scratch/turn_cap/check.py` for N ≤ 16 (cap 2m − 1 fails at 15, 16 as player 2; the exact cap draws).
- **Literature.** Not searched.
- **Metric.** A2 (shelved): unchanged (the exact two-pick class holds to 24).
- **Meaning.** The earlier "fails at a = 1 for every p ≥ 3" was mostly the flaw. Draws reported by `lead_regime` before the fix stand (the flaw only weakened D); its other failures (results/lead-regime-r2.md, other caps) may be too pessimistic.

### 2026-10-26: ideator on the whole problem: a token lemma halves the target (A7, A8)

- **Claim / question.** Fresh ideas for proving L1 itself, after L24 (fresh-idea unit, open brief).
- **Approach.** Ideator (effort max), scratch `scratch/ideator/fresh/`; all its numbers unchecked.
- **Outcome.** (1) Token lemma: at a level position with t = min R, V(R − {t}, t) = draw implies a draw; with t = 1, L1 for N ≡ 3 mod 4 needs only TI at height 2 (block {2..N}, p odd); hand-checked by me, now nodes L26, L27, refuter in proof mode running. (2) A two-pick world at height 2 for the N ≡ 3 mod 4 half (its data came from the flawed `lead_regime`; with the fix, cap 2m − 1 draws every block p ≤ 9 at a = 2). (3) One height-free strategy covers heights down to about p + 2 (p = 4..7), below Hyb2's 2p − 1, but covering (1/2, 2p + 1] needs about p − 2 strategies. (4) TI holds at every real height h > 1/2 for p ≤ 7 (rational h = arithmetic progressions); rows are not robust there, so a descent must carry g0 by a strategy. Dropped: canonical turns, min-first, fixed rules at h → 0+, t_p at every height, induction by four from below (19 sparse failures within {1..22}, e.g. {1..4} ∪ {12,13,15,19,21} a player-1 win).
- **Refuter.** Proof mode on L26, L27 running.
- **Literature.** Ideator: no proof announced; Cooper–Dutle "Greedy Galois Games" (arXiv 1110.1137) has the Thue–Morse order of always-max play on {1..N} but no item choice, so it does not apply.
- **Metric.** None yet (L26 pending its verdict).
- **Meaning.** If L26 survives, the goal is exactly TI(1, p even) ∧ TI(2, p odd), and half of it lives at height 2, where two-pick turns still draw.

### 2026-10-26: Hyb2 can take over once the set is high (A8, B35)

- **Claim / question.** A8's feasibility: if D plays freely while the set is low and Hyb2 from the first high position (min ≥ span) on, does it still draw {1..N}?
- **Approach.** `low_high` with a memoryless Hyb2 high phase (a8a9b7b); [results/low-high-hyb2-n24.md](results/low-high-hyb2-n24.md).
- **Outcome.** Yes for every even-total N ≤ 24, in both roles; also when switching later (min ≥ 2·span). Switching earlier fails (min ≥ span/2: from N = 7). With only the 8 smallest numbers before the switch it fails at 23, 24; the 12 smallest suffice to 24.
- **Refuter.** Not run (feasibility data; the Hyb2 rule matches L24 on blocks).
- **Literature.** Not searched.
- **Metric.** A8: the high phase is settled as Hyb2 for N ≤ 24; left: describe the class H of switch positions the low phase can force (Hyb2 fails on about 6% of high positions, log 2026-10-26: Hyb2 is not a universal high-phase strategy).
- **Meaning.** A proof along A8 needs only the low phase plus a description of the hand-over positions; L25 already bounds the debts after it. The bottom-k window must grow with N, so the low phase is not just "make change from the bottom".

### 2026-10-26: token lemma survives proof mode and is formalized (A7, A8)

- **Claim / question.** L26 (token lemma) and L27 (L1 ⟸ TI(1, p even) ∧ TI(2, p odd)): proof mode, then Lean.
- **Approach.** Refuter in proof mode with its own literal `valueAux` port; Lean from the scratch draft (`CatchUp/Token.lean`).
- **Outcome.** SURVIVES (fixes: x > t, non-emptiness, erase commutation, hypotheses at score 0). Formalized: `CatchUp.token_lemma`, `CatchUp.even_triangle_iff`, `CatchUp.conjecture_of_two_families`; `lake build --wfail` clean, standard axioms. So, kernel-checked: the conjecture follows from draws on {1..N} for N ≡ 0 mod 4 and on {2..N} at deficit 1 for N ≡ 3 mod 4. Also: `turn_cap ranges 2 18 1 2 2`: the two-pick class draws {2..N} at deficit 1 for every N ≤ 16 with even parity (both N mod 4 classes), so via L26 both halves can be posed at height 2.
- **Refuter.** Proof mode (2026-10-26): SURVIVES; all nonempty R ⊆ {0..17} (109,998 satisfying the hypothesis) level draws; A278587 reproduced for N = 3..19. Side pattern (unchecked beyond {0..15}): whenever a level option draws, no level option wins.
- **Literature.** Refuter: no reduction relating {1..N} to {2..N} found (MPRA paper and Feng thesis not readable here).
- **Metric.** A7/A8: the target shrinks from TI at height 1 for all p to TI(1, p even) ∧ TI(2, p odd), now a Lean-checked reduction.
- **Meaning.** The N ≡ 3 mod 4 half lives at height 2, where the two-pick regime with cap 2m − 1 holds for every p ≤ 11 (`lead_regime blocks 11 2 2 1 -1 2`). The refuter's side pattern, if true in general, would be a strong level-position law (B46).

### 2026-10-26: the token works at any rank: a level law (A7, A8, B46)

- **Claim / question.** The refuter saw L26's conclusion hold with the token at any rank, and "a drawing level option excludes a winning one" (B46). Is there a proof?
- **Approach.** Paper: the copying argument of L26 with a pick y < t answered by t, which catches up and leaves the mover at the very node the hypothesis game reaches after its mover's y. Node L28 with a full proof; Lean draft `scratch/lean/Level.lean` compiles (standard axioms).
- **Outcome.** L28 stated (conjecture until proof mode): at a level position, if some pick draws then no pick wins. B46 answered by it and removed from the backlog.
- **Refuter.** Proof mode running.
- **Literature.** Not searched (refuter will).
- **Metric.** None yet.
- **Meaning.** L1(N) ⟺ some opening t of {1..N} leaves player 2 drawing at deficit t; "player 1 cannot win" comes for free once one opening draws. The same holds at every exact tie during play.

### 2026-10-26: the level law survives proof mode and is formalized (A7, A8)

- **Claim / question.** L28 (at equal scores, one drawing pick excludes winning picks) in proof mode, then Lean; L29 (one family at height 2).
- **Approach.** Refuter in proof mode with its own literal port (`scratch/refuter/l28/`); Lean `level_law` in `CatchUp/Token.lean`, `token_lemma` derived from it; `conjecture_of_height_two` (L29).
- **Outcome.** SURVIVES; formalized (`lake build --wfail` clean, standard axioms). Kernel-checked now: the conjecture follows from V({2..N}, 1) = draw for every even-total N (`conjecture_of_height_two`), and value({1..N}) = draw iff some opening draws. The refuter's stronger form (same argument): at a level position at most one pick wins, and then every other pick loses. L29's proof-mode verdict pending.
- **Refuter.** Proof mode (2026-10-26): SURVIVES (all R ⊆ {0..17} at every rank; A278587 to N = 20; Feng 2024 is a different statement).
- **Literature.** Refuter: nothing like the level law found.
- **Metric.** The goal is one family at height 2, V({2..N}, 1) = draw, in Lean.
- **Meaning.** Every exact tie in play is governed by the level law; a defender that can always reach a drawing option at a tie gets the draw for free there.

### 2026-10-26: L29 survives proof mode; its necessity claim corrected (A7, A8)

- **Claim / question.** L29: V({2..N}, 1) = draw for all even-total N implies L1; and the stated converse from N = 12.
- **Approach.** Refuter, proof mode (resumed L28 refuter).
- **Outcome.** The implication SURVIVES → L29 formalized (Lean was already in the strict build). Corrects "2026-10-26: the level law survives proof mode and is formalized": the converse is not proved (L1 gives some drawing opening, not opening 1); it holds for even-total N ≤ 35 by data, where opening 1 always draws.
- **Refuter.** Proof mode (2026-10-26): SURVIVES for the implication; necessity wording wrong, fixed.
- **Literature.** Not searched (covered by the L26 and L28 runs).
- **Metric.** Unchanged (the goal in Lean is the family V({2..N}, 1) = draw).
- **Meaning.** A proof of the family proves L1; a failure of the family would not refute L1.

### 2026-10-26: two-pick turns hold on every low block to p = 13 (A8, B43)

- **Claim / question.** B43: does the two-pick regime hold uniformly at height 2 (the N ≡ 3 mod 4 half), and at height 1?
- **Approach.** `lead_regime blocks` at a ≤ 2 with cap 2m − 1 (p ≤ 11, 13) and with the new exact cap s2 (sum of the 2 smallest left, p ≤ 13). [results/two-pick-blocks-low.md](results/two-pick-blocks-low.md). Also probed (scratch `scratch/a8/hyb2_low.py`): Hyb2 extended to two-pick turns (cheapest turn leaving the opponent past the matching cost, else the largest) fails at every height below 2p − 1 for p ≥ 3.
- **Outcome.** Exact cap: every block p ≤ 13 at heights 1 and 2 draws in both roles. Cap 2m − 1: fails at a = 2 for p = 13 and at a = 1 from p = 8. So the two-pick world is uniform to p = 13 with the exact cap, not with 2m − 1.
- **Refuter.** Not run; s2 matches `turn_cap` and the independent script on {1..N} to 16.
- **Literature.** Not searched.
- **Metric.** A8/A2: the two-pick class holds on all blocks at heights 1, 2 to p = 13 (26 numbers).
- **Meaning.** The ideator's test passes in its exact form: a proof can work in a game where every turn of both players has at most 2 picks, but the cap must be "the opponent's 2 smallest numbers", not a fixed multiple of the smallest. The naive Hyb2 extension is not the strategy there.

### 2026-10-26: Lean: the invariant method on arbitrary positions (A2, A8)

- **Claim / question.** Any strategy proof of L29's family (A8's phases, an A2 class) needs: classes of positions closed under the defender's chosen picks and all opponent picks, level-or-better at the end, imply the defender never loses. `valueAux_transfer` gives this only on translated rounds games.
- **Approach.** Lean helper `CatchUp.valueAux_of_invariant` (`CatchUp/Invariant.lean`): classes `KZ R sZ sY` (Z to move) and `KY R sY sZ` (Y to move) on real positions with scores, strong induction on the numbers left.
- **Outcome.** Formalized; `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound. Also probed (scratch `scratch/a8/threshold.py`, dropped): at low heights there is no loss threshold like L20's matching cost, since a large deficit is caught up over many picks.
- **Refuter.** Not run (a helper checked by Lean, not a blueprint node).
- **Literature.** Not searched.
- **Metric.** None (a tool).
- **Meaning.** A future strategy for the two-pick game or for A8 can be proved by exhibiting its classes and checking closure, without new game-tree induction.

### 2026-10-26: L29's family holds in the two-pick class to N = 28 (A8, B43)

- **Claim / question.** Does the two-pick class (exact cap) hold on L29's family {2..N} at deficit 1, both residues, beyond N = 16?
- **Approach.** New `lead_regime ranges` mode (32d2810); [results/two-pick-height2-family-n28.md](results/two-pick-height2-family-n28.md). Two quick probes (scratch `scratch/a8/mono.py`, `onepick_law.py`), both negative: values are not monotone in the deficit even by steps of 2 ({2, 3}: draw trailing by 1, win trailing by 3, since a big deficit lets the mover take more); and the level law fails off ties ({3, 4, 5} trailing by 2 has a drawing and a winning pick).
- **Outcome.** Every even-total N ≤ 28: D draws {2..N} at deficit 1 in both roles with both players' turns ≤ 2 picks.
- **Refuter.** Not run (search data; the mode matches `turn_cap` to N = 16).
- **Literature.** Not searched.
- **Metric.** A8: the two-pick class holds on the whole Lean target family to N = 28.
- **Meaning.** The game a proof must handle can be taken to be the two-pick game on {2..N} at deficit 1. Copying lemmas like L26/L28 are special to exact ties.

### 2026-10-26: review ideator: two-token lemma makes the root one-sided (A8, A2)

- **Claim / question.** Ideas after L26–L29 (review ideator, open brief).
- **Approach.** Ideator (effort max), `scratch/ideator/review3/`; unchecked unless Lean says so.
- **Outcome.** (1) Two-token lemma: at a tie, if the opponent cannot win after t, it does not lose after any other pick; two such picks give a draw. Roots: L1 ⟸ "player 2 cannot win after openings 1 and 2", or ⟸ "the mover does not win {2..N} nor {3..N} at deficit 1"; Lean draft compiles. Nodes L30, L31 (refuter in proof mode running). (2) Partner exit for A8's high phase: opponent to move behind by e on a high set with c(O) ≤ e ≤ a − c(O): partner replies keep it; never a mover win at draw parity (0 of 163,835), but not forceable as all of H. Dropped, with data: feature-based potentials for the two-pick game (17–21% irreducible error, not closed, no generalization across N), all 5,040 preference orders over 7 reply types (fail by N = 7), canonical safe-reply shape classes (holes up to N − 3), one-pick opponent turns, an inert bottom quadruple, "draw iff g ≤ c(O)" as H (74%), leader matching bound on low sets, simple defender variants (tie-first, tie-avoiding, constant caps).
- **Refuter.** Proof mode on L30, L31 running.
- **Literature.** Ideator: no announced proof; von Stengel's abstract (computation to 28, induction proof wanted) is the newest relevant source.
- **Metric.** None yet.
- **Meaning.** A strategy proof now needs only one role (the leader's defense) from two starts. Searching for a potential of the two-pick game by features is exhausted; a strategy-specific invariant is the remaining route there.

### 2026-10-26: the two-token lemma survives proof mode and is formalized (A8, A7)

- **Claim / question.** L30 (at a tie, if the opponent cannot win after t it does not lose after any other pick) and L31 (L1 from one-sided statements at two starts).
- **Approach.** Refuter in proof mode with its own literal and deficit ports (`scratch/refuter/l30/`); the ideator's Lean draft ported into `CatchUp/Token.lean` (module header, two long lines wrapped, `Finset.single_le_sum` replaced), with `level_law` rederived from the shared copying step.
- **Outcome.** SURVIVES (three wording gaps fixed). Formalized, strict build clean, standard axioms: `level_option_ne_loss`, `two_token`, `conjecture_le_three` (L1 for N ≤ 3), `conjecture_of_leader_pair`, `conjecture_of_suffix_pair`. Kernel-checked now: L1 follows if, for every even-total N ≥ 4, the mover does not win {2..N} trailing by 1 nor {3..N} trailing by 1 (scores 1, 2). Also probed (scratch `scratch/a8/deficit_law.py`): the copying law fails already at deficit 1 ({2,3,4,6} has a drawing and a winning pick), so these reductions stop at ties (O12).
- **Refuter.** Proof mode (2026-10-26): SURVIVES; (a), (b) hold for every even-total N ≤ 24 (own port).
- **Literature.** Refuter: nothing on two-token-type lemmas for Catch-Up; von Stengel's abstract (computation to 28, induction proof wanted) is the newest relevant source.
- **Metric.** A8: the target in Lean is one role (the leader's defense) from two starts.
- **Meaning.** A strategy proof needs only one player's defense: the leader by 1, opponent to move, on {2..N} and on {3..N}.

### 2026-10-26: two-pick class on {3..N} at deficit 1 holds to N = 28 (A8, B43)

- **Claim / question.** L31 (b)'s second start, {3..N} at deficit 1, in the exact two-pick class; and whether one role allows a smaller class.
- **Approach.** `lead_regime ranges 3 28 1 s2 2`, [results/two-pick-suffix3-n28.md](results/two-pick-suffix3-n28.md). One-role probes on {2..N} and {3..N} (N ≤ 20): D ≤ 1 pick with the exact cap; cap m (the opponent catches up in one pick) with D ≤ 2 picks; D ≤ 1 pick with no cap.
- **Outcome.** {3..N}: D draws in both roles for every even-total N from 4 to 28. The one-role classes all fail by N = 7–12 in both roles (e.g. D ≤ 1 pick: L from N = 7; cap m: L from N = 11, D as the other from N = 12).
- **Refuter.** Not run (search data; same engine and mode as the {2..N} run).
- **Literature.** Not searched.
- **Metric.** A8: both starts of L31 (b) hold in the two-pick class to N = 28.
- **Meaning.** One role does not buy a smaller class: the leader needs the full two-pick freedom, as the defender does in both roles.

### 2026-10-26: the high phase is never the obstacle, but its class has no short description yet (A8, B35)

- **Claim / question.** A8's hand-over class H in provable terms: from L31's starts and {1..N}, can D force the first high round start into W ≤ height (L25) plus an outcome class built from formal pieces (L23's depth class, e ≥ c by L20)?
- **Approach.** New experiment `formal_entry` (86fda13); [results/formal-entry-n24.md](results/formal-entry-n24.md). Outcome parts: L23 or e ≥ c; that plus Hyb2T's exact guarantee on ≤ k offsets; Hyb2T's exact guarantee. Cross-check: L23's class lies inside Hyb2T's guarantee at every scored position to N = 20. Scratch `scratch/a8/four_table.py`: Hyb2T's safe debts on 4 offsets, piecewise and irregular ({0,2,3,5}: Z safe at d = 0, 4, not 2).
- **Outcome.** The debt part W ≤ height is always forceable. Outcome: L23 or e ≥ c only to N = 16; with exact 4-offset tables to 20; with 6-offset tables, and with Hyb2T's full guarantee, to N = 24 (scope). Bottom-4 low play with the 4-table: only to 12. All three starts, both roles, the same.
- **Refuter.** Not run (search data; the class code checked against the engine).
- **Literature.** Not searched.
- **Metric.** A8: H described explicitly and forceable: to N = 16 by formal pieces alone, to N = 24 with Hyb2T's exact guarantee on sets of ≤ 6 offsets.
- **Meaning.** A Hyb2T high phase is enough for every N tested, and its debt side is already proved (L25); the open part is a short, provable description of where Hyb2T is safe on general high sets, since the exact table needed grows with N. This is the same kind of gap as A7's rows, now on arbitrary high sets.

### 2026-10-26: high-set safety has no threshold structure in the debt (A8, A7, B35)

- **Claim / question.** Could H's outcome side be described per offset set by a debt threshold (the mover safe iff d ≤ φ(T), the other iff e ≥ θ(T), at the parity of ΣT), for Hyb2T or for optimal play?
- **Approach.** Scratch probes `scratch/a8/hyb_thresholds.py` (Hyb2T's guarantee) and `exact_thresholds.py` (exact rounds-game values) over every T ∋ 0 with |T| even within {0..10}.
- **Outcome.** No. Hyb2T: the mover's safe debts have gaps in 175 of 512 sets ({0,2,3,4}: safe only at d = 3), the other player's in 59 ({0,3,4,6}: 1, 5, 7, …). Exact values: the mover's safe set has gaps in 84 of 512 ({0,2,3,5}: safe at d = 0 and 4, not 2), the other's in 28.
- **Refuter.** Not run (scratch probes; the exact recursion is the one in `hyb2_universal`).
- **Literature.** Not searched.
- **Metric.** None (an obstruction, O14).
- **Meaning.** H cannot be cut out by debt thresholds per set, whatever the high strategy; a description has to restrict the sets themselves (like L23's depth or blocks), and the low phase has to steer into such sets.

### 2026-10-26: review ideator: a halving induction (A9, A8, A4)

- **Claim / question.** Ideas after the review of 79 log entries (open brief: best chance of proving the conjecture).
- **Approach.** Ideator (effort max), `scratch/ideator/review4/`; unchecked unless stated.
- **Outcome.** (1) Halving induction, new line A9: the defender plays margin-optimal moves of the bottom-half game (recursively along N, ⌊N/2⌋, …) until the opponent first picks in the top half; the top half {⌊N/2⌋+1..N} is an even block exactly at L24's threshold a ≥ 2p − 1, in every residue. R_N draws for every even-total N from 7 to 24 in both roles and on ({2..N}, 1), with any optimal choices; the cut at ⌊N/2⌋ is sharp; keeping only the low game's value fails at N = 20. Escalation positions (after the opponent's first top-half pick) are D-draws at all 9,778 positions for N ≤ 20; answering h − 1 draws at 99.4%. Needs: the margin bound one size down (odd totals: ≥ −3 measured), L24 with B38's band, an escalation lemma. (2) Change-pool law (A4): {1..k} ∪ H with 2·max H ≤ 1 + … + k draws at its parity gap (no failure to U = 22–24). (3) A sharper two-pick class (B43). Dropped, with data: pool-matching defender, a complete-multiset law (fails at U = 22), greedy low play (margin too low near N = 36), fixed escalation answers, multi-level follow-suit, symmetric sets (O15: {1,6,8,9,14,15,17,22} is a mover win; checked here with an independent solver).
- **Refuter.** Claim mode on A9's search results requested.
- **Literature.** Ideator: nothing new, no announced proof.
- **Metric.** A9: R_N draws to N = 24 (unchecked).
- **Meaning.** A route by induction on N in which the top half is already in a proved regime and the bottom half is the same game one size down; the open part is one escalation lemma. Main line moved to A9 (under Awaiting review).

### 2026-10-26: L24 and L25 formalized: even blocks draw from height 2p − 1 (A7, A8)

- **Claim / question.** L25 (Hyb2's potential W never rises over a round) and L24 (the block {a..a+2p−1} draws at a ≥ 2p − 1) in Lean.
- **Approach.** Index-free zones (`OddBelow`, `oddPts`, `evenPts`, η as even holes); T1–T4 as separate theorems; L24 through `valueAux_transfer` with explicit classes `HZw`, `HYw`: L23's class before the switch or e ≥ c after, parity, W ≤ 2p − 1. Fallback answer AM+T's (the refuter's route). Draft `scratch/lean/Hyb2L25.lean` (zone tools partly by a helper agent), then `lean/CatchUp/Hyb2.lean`; tests `Tests/BlockDrawHyb2.lean`.
- **Outcome.** `potW_z_round`, `potW_y_round`, `block_row_draw_hyb2`, `block_draw_hyb2`: `lake build --wfail` clean, axioms propext, Classical.choice, Quot.sound. Deviations (blueprint L24, L25): AM+T fallback; L23 instead of L15; explicit classes instead of reachable starts; Z's debts bounded directly; T4 split by the answer's side.
- **Refuter.** Proof mode earlier on both (SURVIVES); Lean checks the rest.
- **Literature.** Not searched.
- **Metric.** A7: Lean-checked TI for every p at a ≥ 2p − 1 (was a ≥ 6p − 2). A8: the high phase's debt side (W) Lean-checked.
- **Meaning.** High blocks are machine-checked down to Hyb2's tight height; `block_draw_hyb2` has `block_draw_linear`'s statement with a weaker hypothesis, so it is the one to approve if blocks are reported.

### 2026-10-26: A9's search claims survive the refuter to N = 28 (A9, B49)

- **Claim / question.** Refuter, claim mode, on A9's claims: R_N draws for even-total N in both roles and on ({2..N}, 1); the one-level version and its cut; every escalation position is a D-draw.
- **Approach.** Two independent re-implementations (`a9.rs` on compressed states, `brute.rs` literal; equal on N = 3..16, 19, 20); values reproduce [results/values-n1-31.md](results/values-n1-31.md) to N = 28 and A278587; `scratch/refuter/a9/`.
- **Outcome.** SURVIVES. R_N draws for every N ≡ 0, 3 (mod 4) from 3 to 28 (27 and 28 were B49), with adversarial and friendly tie-breaks; one level also; ⌊N/2⌋ ± 1 fail at N = 15, 16, but ⌊N/2⌋ − 1 draws at N = 4, 7, 11. Escalation positions are never D-losses (24 / 228 / 2,456 / 7,070 at N = 8 / 12 / 16 / 20, 195,468 at N = 28). Corrections: "D has a drawing answer inside the top half" is false from N = 24 (7 positions; {2,9,12} ∪ {14..24} after E took 13, D trailing by 4: only 2, 9, 12 draw, re-checked by `scratch/a9/pos_check.py`, an independent solver); "h − 1 draws at 99.4%" was a rule with fallbacks at N = 20 (plain h − 1: 89.7% at 20, 91.7% at 24); "9,778 for N ≤ 20" sums N = 8, 12, 16, 20 only. "Take the largest of the active prefix" draws to N = 19, so small N does not single out margin-optimal play.
- **Refuter.** This entry: SURVIVES.
- **Literature.** Refuter: A278587 has no strategy comments; two searches found no halving or prefix strategy and no announced proof.
- **Metric.** A9: R_N draws to N = 28 (refuter-checked).
- **Meaning.** The stretch before the first escalation is solid to N = 28; the escalation lemma cannot be an answer inside the top half.

### 2026-10-26: escalation needs free play: no answer rule, no return to R (A9, B48)

- **Claim / question.** B48: a describable first answer at escalation positions, and whether one exchange returns play to R's domain.
- **Approach.** Ideator (resumed), `scratch/ideator/review4/esc5.rs`–`esc11.rs`, `recur*.rs`; unchecked.
- **Outcome.** No. h − 1 else h + 1: 99.4% at N = 20; Hyb2 on the top half: 96.7%; the best choice between them, even by oracle: 99.5% (32 positions at N = 20 where neither draws). Rules over 8 candidate answers reach 7,061 / 7,070 only with thresholds fitted per N. Failures sit at the end of the low phase (1–4 low numbers left). After one exchange, R's isolated-optimal low play fails from N = 7 (single best answer) or N = 15 (a whole free answering turn); only "D never starts the top half, answers each entry with a free turn, plays its best low moves" holds (to N = 20, `suit3` to 24).
- **Refuter.** Not run (negative search results; the one positive form is a value statement, not a claim to check).
- **Literature.** Not searched.
- **Metric.** A9 (c) in describable form: no rule settles every escalation position (best 99.4% at N = 20).
- **Meaning.** After an escalation D needs free play and low play that sees the top half; A9's kill criterion "the escalation lemma needs free play with no describable answer" is met (O16), and what is left of (c) is a value statement on mixed positions, as hard as A8's (ii).

### 2026-10-26: A9's prefixes must be the fixed halving chain (A9)

- **Claim / question.** Is R_N's halving chain essential, or does a prefix adapted to the opponent's picks work too (D plays the best-margin move of the game cut at {1..min(N, f·x)}, x the largest number E has picked)? Such a rule would describe play after an escalation.
- **Approach.** The refuter's checker (`scratch/refuter/a9/a9.rs`) with other chains, `scratch/a9/prefix.rs`: every prefix as a level; levels moved out one at a time or, when used up, straight to free play; f = 1, 1.5, 2, 2.5, 3; adversarial and friendly tie-breaks; even-total N ≤ 20.
- **Outcome.** All fail. f = 1 fails from N = 4 (P2 after E opens a high number); a continuous top half with halving inside fails from N = 4; f = 1.5–3 fail with adversarial ties from N = 3–7, with friendly ties f = 2 fails at N = 7, 11, 15, 19 and f = 2.5, 3 at N = 8, 12, 16 or 19. The halving chain itself draws at every N in the same runs.
- **Refuter.** Not run (negative search on the refuter's own code).
- **Literature.** Not searched.
- **Metric.** None (A9 shelved; a variant ruled out).
- **Meaning.** R_N's success depends on fixed nested levels N, N/2, N/4, …, not on scaling D's horizon to E's picks; an escalation rule cannot simply re-centre the prefix on E's pick.

### 2026-10-26: correction to "A9's prefixes must be the fixed halving chain" (A9)

- **Claim / question.** The friendly-tie failures listed in that entry.
- **Approach.** Re-read of the same run's output (`scratch/a9/prefix.rs`, N ≤ 20).
- **Outcome.** With friendly ties: f = 2 fails at N = 7, 11, 15, 19; f = 2.5 at N = 8, 12, 16, 19; f = 3 at N = 7, 19 (the entry grouped f = 3 with f = 2.5). The conclusion stands: every factor fails.
- **Refuter.** Not run.
- **Literature.** Not searched.
- **Metric.** None.
- **Meaning.** Unchanged.

### 2026-10-26: `block_draw_hyb2` audited: it says what we mean (A7)

- **Claim / question.** Does the Lean statement `block_draw_hyb2` (L24) say what its plain reading says, with no trap at the new height boundary a = 2p − 1?
- **Approach.** `audit-statement`: tests in `Tests/BlockDrawHyb2.lean` (Catch-Up on the block for p even; implies `block_draw_linear` and, added now, `block_draw_high` for every p ≥ 1); refuter in statement mode with two engines of its own (`scratch/refuter/hyb2stmt/`).
- **Outcome.** No gap: literal reading, ℕ subtraction, the flag, the base score and the boundary cases (p = 1, a = 2p − 1) check out; the claim and every row hold for p ≤ 7 at a ∈ [2p − 1, 2p + 5] and p = 8 at a = 15, 16. The block still draws at a = 2p − 4..2p − 2 (p ≤ 8), so 2p − 1 is the proof's limit, not the game's; the rows version does need it ({2,3,4,5} at deficit 2 is a mover win). Doc comment marked pending approval.
- **Refuter.** Statement mode: SAYS WHAT WE MEAN.
- **Literature.** Refuter: nothing on blocks or consecutive sets beyond the README's sources; no proof announced in 2026.
- **Metric.** A7: unchanged (the statement is ready for approval).
- **Meaning.** If blocks are reported, `block_draw_hyb2` is the one statement to approve; it covers the two earlier block theorems.

### 2026-10-26: blocks draw at every real height (L32, conjecture) (A7, B45)

- **Claim / question.** B45: is TI robust to non-integer heights, i.e. is B(h, p) = {h..h+2p−1} at debt p mod 2 a draw for real h?
- **Approach.** p = 8 at every breakpoint r/s (s ≤ 16) on (0, 17] (`scratch/b45/genbreak.rs`, the ideator's code with a range option; 10 min); opening outcomes over h for p = 2, 4, 6 (`scratch/b45/openings.py`); refuter in claim mode with an exact parametric solver (h symbolic) and integer engines.
- **Outcome.** For p even: a draw at every real h > 0, exactly for p = 2, 4, 6, 8 (whole of (0, ∞)). For p odd: draw from h = 1/2 for p = 3, 5, 7 (exact), from 2/5 for p = 9 and 1/3 for p = 11 (sampled), from 1 for p = 1; below, the mover wins. My claimed converse (a mover win at every h ≤ 1/2) was false: h = 1/2 is a draw. The second smallest opening draws on (0, ∞), (0, 8), (0, 11) for p = 2, 4, 6. New conjecture node L32; by scaling, every arithmetic progression of 4m terms is a draw.
- **Refuter.** Claim mode: the draw part survives (exact for p ≤ 8); the converse BROKEN (corrected in L32: no converse claimed). It also found that the scripts' range (0, 2p + 1] left non-integer h up to p(2p − 1) + 1 unchecked; its exact runs cover them for p ≤ 8.
- **Literature.** No Catch-Up results on arithmetic progressions or real numbers (six searches in all).
- **Metric.** A7: TI at real heights checked exactly for p ≤ 8 (was: sampled, p ≤ 7).
- **Meaning.** The block draws do not depend on integrality, so a proof can use h as a continuous parameter: the value can change only at breakpoints, and only through near-tie positions (L32's section). B53 tests whether those are always draws on the defender's lines.

### 2026-10-26: no drawing strategy works across all heights (L32, A7, B53)

- **Claim / question.** Does either player have one drawing strategy on B(h, p) that works at every real h, using only what play reveals about h (who moves when)? Such a strategy could not depend on the sizes of the numbers, so it might be describable.
- **Approach.** `scratch/b45/robust.py`: the game with h unknown in an interval (adversarial); X's lead is dk·h + dc, play narrows h to an interval, and X's value is max over its picks, min over the opponent's and over the h-ranges play cannot distinguish (generic h). Checked against the exact values (p = 1 win below 1, p = 3 win below 1/2). `cover.py`: the fewest h-intervals on which each player has one strategy (greedy over breakpoints r/s, s ≤ 2p).
- **Outcome.** One strategy for all h > 0 exists only for p = 2 (both players). Otherwise the fewest ranges (generic h; for P2 at odd p from 1/2): p = 3: P1 (0, 6), (6, ∞), P2 one; p = 4: P1 (0, 4), (4, ∞), P2 (0, 6), (6, ∞); p = 5: P1 (0, 4), (4, 8), (8, ∞), P2 (1/2, 3), (3, 8), (8, ∞); p = 6: P1 (0, 3), (3, 6), (6, 10), (10, ∞), P2 (0, 3), (3, 7), (7, ∞); p = 7: P1 (0, 3), (3, 5), (5, 8), (8, 14), (14, ∞), P2 (1/2, 2), (2, 5), (5, 10), (10, ∞). Every boundary is an integer. P1's robust strategy for p = 4 on (0, 4) opens with the smallest number; its replies show no evident rule.
- **Refuter.** Not run (scratch search; the solver reproduces the exact values above).
- **Literature.** Not searched.
- **Metric.** None (O17).
- **Meaning.** Drawing play must know roughly which integer band h lies in, and the number of bands grows with p, so L32 does not come with one strategy uniform in the height; a descent in h (B53) has to switch strategies at integer heights. Within a band one strategy covers all real h, so integrality itself is never used.

### 2026-10-26: review ideator: moving quadruples, and where low play meets Hyb2 (A10, A8)

- **Claim / question.** Ideas after the review of 87 log entries (open brief: best chance of proving the conjecture).
- **Approach.** Ideator (effort max), `scratch/ideator/review5/`; everything unchecked.
- **Outcome.** (1) Moving quadruples, new line A10: H(M, k) = "{1..M} plus k far 4-blocks draws at its parity gap"; L1(N) = H(N, 0), and H(M, k) ⇐ H(M − 4, k + 1) ∧ Const(M, k), where Const says V({1..M−4} ∪ ({M−3..M} + c) ∪ far blocks) does not depend on c ≥ 0. No non-draw of Const found (N ≤ 16 to c = 120, N = 19, 20 to c = 400, N = 23, 24 to c = 60; with one far block to N = 16, two to N = 12); unlike O17, one strategy draws every shift c at once (N ≤ 16, both roles). The direct simulation proof fails (D needs low "change grabs" in the far game). (2) A8: smallest-first play is safe in a deep class (min R < 0.3·span, D's numbers below min R) to N = 24 position-wise, but steers into hand-overs Hyb2 loses (smallest-first below 0.2·span with Hyb2 once high fails at N = 23, 24); the separating feature of those hand-overs is the open question. (3) A8 (ii) reduced to the deep class's exits, a conjecture to test beyond N = 24 with suffix tables. (4) A8's window of smallest numbers grows (k = 4 fails at 19, 5 at 23, 6 holds to 24), toward its kill criterion. Dropped, with data: a spine chain into L24 (P_N(k* − 1) is a mover win for N = 24, 28, 31, …), rounds play with boundedly many breaks (D needs about N/8), deque reduction, partner menus, smallest-plus-one turns, a single switch to Hyb2, other change pools (O3's set is a pool), rows at real heights.
- **Refuter.** Not run yet; A10's data is the first candidate.
- **Literature.** Ideator: three searches, seven sources opened; no proof or new result announced, nothing on deformations or far blocks.
- **Metric.** A10: Const checked to N = 20 (c ≤ 400), unchecked.
- **Meaning.** A10 is the first reduction of L1 to a deformation in which only four numbers move, with evidence that one strategy covers the whole deformation, which is exactly what O17 showed blocks lack. A8 gets a sharper question at its hand-over and a kill-criterion check.

### 2026-10-28: Const holds at N = 19 with one far block (A10, B54)

- **Claim / question.** B54, second part: does Const(19, 1) hold, i.e. is V({1..15} ∪ ({16..19} + c) ∪ E_1) at its parity gap a draw for every c? A non-draw kills A10.
- **Approach.** `scratch/a10/deform_list.rs` (the ideator's `deform2.rs` with an explicit list of shifts; same memoized solver), c ∈ {0..10, 14, 20, 30, 45, 60, 90, 120, 180, 250, 400}; 7 min, 34M states; output `scratch/a10/deform_list-19-1.txt`. Sanity: N = 8, 12 small cases draw as before.
- **Outcome.** Draw at every sampled c.
- **Refuter.** Running, claim mode, on the ideator's Const data, the far-spacing claim, A10's reduction and the one-strategy claim (B54, first part).
- **Literature.** Not searched.
- **Metric.** A10: Const at k = 1 sampled to N = 19 (was 16), unchecked.
- **Meaning.** No counterexample yet; the line stands until the refuter's verdict.

### 2026-10-28: far blocks act as a margin tolerance; A10 needs only k = 0 (A10)

- **Claim / question.** What do A10's far blocks do? Candidate MT: with m(S) the margin game's value at a tie (Catch-Up turns, payoff the final score difference, no early-loss rule), V(S ∪ E_k, 0) = draw iff |m(S)| ≤ 2k for every even-sum S. With the sign lemma V = sign(m), this would collapse A10's chain over k.
- **Approach.** `scratch/a10/farblock.rs`: margin table over all subsets of {1..U}, Catch-Up value of S ∪ E_k by a memoized solver; every even-sum S ⊆ {1..13}, k = 0, 1, 2 (output `farblock-13-2.txt`). Margins at a tie on {1..N}, N ≤ 16, reproduce the signs of [results/values-n1-31.md](results/values-n1-31.md) (N = 9, 10, 14 losses, 13 a win; magnitudes 0 or 1).
- **Outcome.** No mismatch in 4,095 sets × 3 values of k, including the three sets with m(S) = −2. FB (a drawn set stays drawn with one far 4-block) holds throughout. Consequence on paper: L1(N) ⇐ L1(N − 4) ∧ FB({1..N − 4}) ∧ Const(N, 0): for c large the moved quadruple is a far block over {1..N − 4}, which draws by L1(N − 4) and FB. So only Const at k = 0 is needed, and A6's Lemma B (the low game with the quadruple as final payoff) follows from L1(N − 4) once MT holds.
- **Refuter.** Running, claim mode (MT, the sign lemma, the reduction).
- **Literature.** Not searched (refuter searching).
- **Metric.** A10: unchanged (a simplification, not a check of Const).
- **Meaning.** Far blocks are a final payoff that only reads the margin; everything A10 needs beyond MT is Const(N, 0): sliding the top quadruple of {1..N} up never changes the value. A6's open half and A10 are the same question.

### 2026-10-28: answering the quadruple at once loses; margin rows are not local (A10, A6, A1)

- **Claim / question.** (1) Proof route for Const: if the defender D reserves the moved quadruple Q and answers every attacker pick in Q with its partner as the first pick of its next turn, the game tree is the same for every c (deficits change by ±1 per exchange), so a far-game strategy would transfer down to c = 0. Does that restricted D still draw? (2) A1 with margins: is v(S ∪ B, d), B a top block, a function of S's margin row near d?
- **Approach.** (1) `scratch/a10/gamma.rs`: free game, A6's reservation (D takes from Q only to close an opened pair or when only Q is left), and strict reservation (that close comes first, while low numbers remain); N = 7, 8, 11, 12, 15, 16; c = 0, 1, 2, 3, 5, 8, 13, 40, 1000; both roles. Independent Python check at N = 7 (`strict_check.py`). A first version applied the strict rule also in the endgame and in the free game (all values −1); fixed. (2) `scratch/a10/mrows.rs`: S ⊆ {1..12}, B of length 2 or 4 at x = 13.., keys (x, d, v(S, d − w..d + w)), w ≤ 4, and the whole row.
- **Outcome.** (1) Free and reservation games draw at every N and c in both roles; strict reservation loses everywhere, from N = 7. Line at c = 0, D second: A 1, D 2, A 4, D must close with 5 (leading 2), A 7, D 6, A 3: A wins by 2; unrestricted, D answers 4 with 3 (a tie) instead. In the far game the same D takes 3 then closes (a "grab"), which leads to a different position, so far-game play cannot be copied down by closing at once. (2) Undetermined keys: pairs 744 / 2,792 / 6,026 / 8,656 / 9,441 for w = 0..4 and 3,176 with the whole row; quadruples 876 to 9,161, and 1,323 with the whole row.
- **Refuter.** Running, claim mode (both negatives).
- **Literature.** Not searched.
- **Metric.** None (negative).
- **Meaning.** Const has no proof by a defender who treats the quadruple as untouchable and closes at once: low change answers to a quadruple pick are essential, at every c. And margins, which settle far blocks exactly (MT), do not make a near block local: O4 holds for margin rows too.

### 2026-10-28: the defender's low window grows like N/4 to N/2 (A8, B57)

- **Claim / question.** B57, A8's kill-criterion check: is there a fixed k such that D, playing among its k smallest numbers while the set is low and Hyb2 once high, draws every even-total N? A k growing with N at every hand-over threshold meets A8's first kill criterion.
- **Approach.** `low_high` at hand-over thresholds min ≥ t·span, t = 1, 2, 3, 4, various k, N ≤ 24 ([results/low-high-window-n24.md](results/low-high-window-n24.md)).
- **Outcome.** Least k by N: at t = 1 it grows to 12 at N = 24 (about N/2); at t = 2 to 7; at t = 4 it is 3, 4, 5, 6 for N ≤ 8, 11–16, 19, 20–24 (about N/4). No fixed k holds at any t.
- **Refuter.** Not run (a search over an existing, checked engine; negative for fixed windows).
- **Literature.** Not searched.
- **Metric.** A8: "largest N for which (ii) holds with a fixed k": k = 6 to N = 24 at t = 4, but every fixed k fails beyond some N ≤ 24 at t ≤ 2.
- **Meaning.** A8's kill criterion holds in its letter for fixed windows, but a late hand-over (t = 4) keeps the window near a quarter of the numbers, which is still a real restriction. A8's low phase, if it exists in describable form, is "the bottom quarter until the set is four times its spread above zero", not a bounded menu.

### 2026-10-28: a far quadruple acts on every margin by one map; near ones do on interval rows (A10)

- **Claim / question.** Is MT exact at the level of positions? MT+: for every S below a far quadruple Q and every deficit d, m(S ∪ Q, d) = ψ(m(S, d)), ψ(X) = X − 2·sign(X) for |X| ≥ 2, X for |X| ≤ 1 (the quadruple played last from the low game's final margin). And for a near quadruple: does {1..M} ∪ Q_c satisfy the same identity at every deficit, every c?
- **Approach.** `scratch/a10/mtplus.rs` (every S ⊆ {1..10}, d ≤ 10; Q at 120; also a far pair); `rowconst.rs` (M ≤ 16, c ≤ 30, d ≤ M); `nearq.rs` (every S ⊆ {1..12}, Q at x ∈ (max S, 19], d ≤ max S), all entries and draw-parity entries (m(S, d) even) only.
- **Outcome.** MT+ holds at all 11,264 (S, d) for the quadruple. For a far pair it fails at 598, all where the low game ends level and ψ would need to know who moves next; the quadruple's own row is 0 at a tie, so it does not care. ψ is monotone on each parity class, so playing the quadruple last commutes with optimal play; the content of MT+ is that opening it early never helps. Near quadruple on intervals: the identity fails only at odd-margin entries (a ±1 win or loss changes sign with c), never at draw-parity entries, for every M ≤ 16, c ≤ 30, d ≤ M; there the entries are 0 for M ≥ 6 (M = 5: row value 2 at d = 3, 5 becomes 0). On all subsets of {1..12} at draw-parity entries: every interval and every set with ≥ 10 numbers is shift-invariant; by holes below max S: 12/12, 62/66, 169/220, 273/495, … sets for 0, 1, 2, 3 holes, the few-hole failures at large deficits ({1,4,5} at x = 8, d = 4).
- **Refuter.** Not yet (MT is with the refuter; MT+ and the band form go next).
- **Literature.** Not searched.
- **Metric.** A10: Const in band form (every draw-parity deficit d ≤ M) to M = 16, c ≤ 30, unchecked.
- **Meaning.** Margins carry the far quadruple exactly, at every position: a candidate lemma (MT+) with a proof by induction on S, where only early openings need an argument. Const strengthens to a band: {1..M} with any quadruple above draws at every draw-parity deficit up to M, a richer hypothesis for an induction. Position-wise the band fails on sparse sets, so any proof must use density along play (as L4, O5).

### 2026-10-28: margin tolerance and the two negatives survive the refuter (A10)

- **Claim / question.** The refuter's verdict on the entries "far blocks act as a margin tolerance" and "answering the quadruple at once loses; margin rows are not local": the sign lemma, MT, the reduction to Const(N, 0), strict reservation, margin rows.
- **Approach.** Refuter, claim mode, own engines (`scratch/refuter/mt/`: `mt.rs`, `res.rs`, `mrows2.rs`, `pyrow.py`).
- **Outcome.** All five survive. MT: no mismatch on all even-sum S ⊆ {1..16} (k ≤ 2) and {1..17} (k = 1), k ≤ 4 on {1..13}, random sparse and large-element sets, other gaps and spacings; it needs sum + g even (odd: V = sign(m), unchanged); spacing x ≥ (total below) − 6 suffices on {1..13}; the margin form m(S ∪ E_k, g) = sign(m)·max(|m| − 2k, |m| mod 2) holds (ψ^k). Reduction valid, FB checked for M ≤ 17 (all subsets) and M = 19, 20; caveat: at c = 0 Const(N, 0) is L1(N), so the reduction helps only via a proof uniform in c; the k ≥ 1 form H(M, k) is ill-defined (collisions with far blocks). Strict reservation genuinely loses; closing within the next turn after low grabs loses too at N = 12 (c ≤ 1) and N = 15, 16 (c ≤ 2). Margin rows: my "whole row" counts were partly a cut-off artefact (rows differing past deficit 16); with full rows and the sum as key 49 pair and 29 quadruple keys stay undetermined, e.g. S = {1,2,3,4,5,9} vs {1,2,4,8,9} under {13..16} at d = 7: win vs loss.
- **Refuter.** SURVIVES (claim mode), with the corrections above.
- **Literature.** Refuter, three searches (margin version of Catch-Up; far or large numbers, thresholds, tempo; scoring games and Milnor's universe): nothing on Catch-Up margins or far-block thresholds; opened arXiv 1505.01907 and 1303.4275, not relevant.
- **Metric.** A10: L34 refuter-checked (all even-sum S ⊆ {1..16}); new nodes L33, L34, L35 (conjectures); O18.
- **Meaning.** The far end of A10 is solid: far blocks only read the margin, so A10 is exactly L35 plus a proof of L34. L35 must be proved uniformly in c, and by a defender that answers quadruple openings with low change (O18).

### 2026-10-28: far adjacent pairs and far quadruples are played last (A10, B58)

- **Claim / question.** B58, first step toward L34 on paper: is a far block optimally left for last at every position, i.e. m(S ∪ B, d) = t_B(S, d), the low game on S whose terminal payoff (mover trailing by e when S runs out) is B's own row m(B, e)?
- **Approach.** `scratch/a10/lastplay.rs`: every S ⊆ {1..11}, d ≤ 11, B at a = 142: {a, a + 1}, {a, a + 2}, {a, a + 3}, {a..a + 3}.
- **Outcome.** Exact for the adjacent pair (row 1 − e) and the quadruple (row 0, −1, 0, −1, −2, …): 0 of 24,576 positions differ. Not for pairs with a gap of 2 or 3 (1,527 and 4,160 differ; early openings matter there). After an early opening of the quadruple, the replier can always take a number that leaves an adjacent pair ({a, a + 1}, {a + 1, a + 2} or {a + 2, a + 3}), so an induction for L34 can use the adjacent-pair case for what follows an opening.
- **Refuter.** Not run (to go with B58's proof).
- **Literature.** Not searched.
- **Metric.** A10: unchanged (L34's proof plan, not a node change).
- **Meaning.** L34 splits into "S-picks commute with ψ" (done on paper in L34's section) and "an early opening never beats playing last", where the opener's best case is bounded by the adjacent-pair game: a finite inequality between the low game with terminal row 1 − e and with ψ.

### 2026-10-28: Const survives the refuter, exact to N = 20 (A10, B54)

- **Claim / question.** B54: the refuter on the ideator's Const data, the far-spacing claim, A10's reduction and the one-strategy claim.
- **Approach.** Refuter, claim mode, own engines (`scratch/refuter/a10/`: literal `valueAux` port reproducing A278587 for N = 3..20, a compact-memo engine for 23–24 numbers, a Python cross-check; `robust.rs` for one strategy over c, controlled by reproducing O17's split heights for p = 4).
- **Outcome.** No non-draw anywhere. With k = 0 every comparison is j·c + b, |j| ≤ 4, |b| ≤ T(N), so the value is constant for c > T(N): L35 holds at every integer c for N ≤ 20, at c ∈ [61, 278] for N = 23, at 22 samples in [61, 301] for N = 24, and at every real c for N ≤ 16; the ideator's own runs had stopped below T(N) at N = 16, 23, 24. One defender strategy in both roles covers every integer c for N ≤ 16 (every real c at N = 8, 11, 12), and with far blocks for small cases. A large enough c gives exactly the canonical far set, so the far-spacing claim is not needed. Proves too much otherwise: with another base B the value moves with c (O19). Const with far blocks along A10's first chain holds at every c checked for N ≤ 20.
- **Refuter.** SURVIVES (claim mode).
- **Literature.** Refuter: A278587 and von Stengel's abstract opened (computation "may help in eventually finding an induction proof"); three searches, no proof, nothing on deformations or far blocks; arXiv 2508.00246 is another game.
- **Metric.** A10: L35 exact to N = 20 over all integer c (was sampled to 24, unchecked).
- **Meaning.** L35 is as solid as the data can make it at these sizes, it needs the interval base, and one c-uniform strategy exists; what is missing is a reason.

### 2026-10-28: ideator on the low phase: the top pair moves exactly, the quadruple does not; a twins homotopy (A10, A8, new A11)

- **Claim / question.** Fresh ideas aimed at the core difficulty, with tonight's margin facts (brief: why Const holds; margin invariants; other deformations).
- **Approach.** Ideator (effort max), `scratch/ideator/fresh28/`; everything unchecked. Its solver reproduces N = 5, 8, 9, 13, O7's C at gap 1, O9's two blocks and B43's class result.
- **Outcome.** (1) RPG, the moving top pair: D never takes {n−1, n} while lower numbers remain, and when O takes one, D's next turn ends with the other (after lower picks that keep D behind). Then no comparison involves c, each player gets one pair element, and the game tree is the same for every real c ≥ 0; RPG meets the margin target in both roles for every n ≤ 24 (`rpgfast.rs`), so L1(n) ⇐ RPG_∞(n), the low game on {1..n−2} with one atomic exchange for O and a far pair absorbing a margin of 1. The same device fails for the quadruple (−2 at N = 11, 12 as P2, 15, 16 in both roles; `rqg*.rs`), for two nested pairs (`nest.rs`) and for close-at-once on 3 or more top pairs (`gtc.rs`); D playing only margin-optimal moves of the game without the exchange falls to −12 at n = 20 (`compat.rs`): D must anticipate the exchange. So a c-uniform quadruple strategy exists (refuter) but plays different trees at different c: L35 is a coincidence of values, not a shared tree. (2) TD, twins to interval: pairs {x, x + t}, x over odd (fam a) or even (fam b) bases, mover trailing by t·(p mod 2); t = 0 is twins (mirror draw), t = 1 is {1..2p} or {2..2p+1} at deficit 1 (L27, L29), so L1 ⇐ TD draws for all t ∈ [0, 1]. Exact over all cells (`tdcells.rs`): draw for every t, fam a p ≤ 8, fam b p ≤ 7; one strategy for all of (0, 1] for p ≤ 6, 2–3 pieces at p = 7, 8 (L32 needs 2, 2, 3, 4, 5 for p = 3..7). (3) A8: escalation-safe low play has no simple predicate (B43's class with RPG fails from n = 7; the deficit against the two smallest numbers does not separate, `vuln.rs`). Dropped with data: a pool tolerance law m({1..k} ∪ H) = sign·max(|m(H)| − T_k, parity) (exact for k ≥ 6 on H ⊆ {k+1..26}, fails on O7-type cores, no closed family); a far pair as a tolerance position by position; moving 1 or 3 numbers.
- **Refuter.** Not run yet (RPG and TD go next).
- **Literature.** Ideator: two searches; only the known sources (A278587, von Stengel, MPRA, Feng, Eastaway's blog); no proof announced.
- **Metric.** A10: none (a structural negative for its strategy route); new line A11.
- **Meaning.** A10's strategy route closes at the quadruple: no restriction makes the quadruple's tree c-independent (with O18). What remains of A10 is value-level (breakpoints of L35, as B53) or one level only (RPG for the top pair). TD is the first deformation whose easy end has an explicit strategy (mirror) rather than high blocks.

### 2026-10-28: near ties on optimal lines flip across L35's breakpoints (A10, B63)

- **Claim / question.** B63: can L35 be proved breakpoint by breakpoint? Crossing c* swaps the two continuations of a near-tie pick (picker a hair behind and moving on, or a hair ahead and handing over), which leave the same numbers R with the roles swapped; if every near-tie pick on optimal lines leads to a draw on both sides of c*, no crossing changes the value (B53's lemma on this family).
- **Approach.** `scratch/a10/crit.rs`: numbers scaled by 1200, c = c* ± 1/1200 for every c* ∈ (1/12)ℤ up to T(N); every node on optimal lines (both players keep the value) from the root; near-tie picks are those with |lead| ≤ 4 scaled units, lead ≠ 0; for each, the swapped node's value on the other side of c*. N = 8, 11, 12 (seconds). A first version only checked the node on its own side, which is a draw on any optimal line from a drawn root: vacuous, replaced.
- **Outcome.** Near-tie picks on optimal lines occur only at integer c* (one quadruple number of imbalance): 1, 7, 10 such breakpoints for N = 8, 11, 12, hundreds of picks each. Their swapped nodes are draws except at 1 breakpoint for N = 11 (c* = 1, 12 picks) and 4 for N = 12 (c* = 1, 2, 3, …), all just below c*; there the swapped node is a win or a loss for the picker (O20).
- **Refuter.** Not run (negative; the flipping nodes are listed with `SHOW=1` and the root stays a draw on both sides, as the refuter's exact values require).
- **Literature.** Not searched.
- **Metric.** A10: B63's strong form fails; L35 unchanged.
- **Meaning.** The value-level route needs the defender to steer around flipping near ties, which is the c-uniform strategy again, the object with no c-independent form (O18). Both of A10's routes now rest on the same undescribed strategy; the same test applies to L32's and A11's breakpoints (B53), where it would decide whether those homotopies can be crossed locally.

### 2026-10-28: TD's interior crossings flip too, rarely (A11, B53)

- **Claim / question.** O20's test on A11: do near-tie picks on optimal lines of TD(p, t) keep their value across interior breakpoints t* ∈ (0, 1)? If they always do, TD crosses locally where L35 does not, a reason to prefer A11.
- **Approach.** `scratch/a11/tdcrit.rs` (numbers scaled by 100·lcm(1..p+1), t = t* ± one unit; every optimal line; swapped node on the other side), fam a and b, p = 2..6 (seconds).
- **Outcome.** Interior breakpoints with near-tie picks on optimal lines are rare (fam a p = 6: t* = 1/2 only; none for p ≤ 5 or fam b p = 6), and at t* = 1/2 for fam a p = 6, 2 of 15 swapped nodes change value (just below t*). The other flips are at t* = 0 and 1, where the test compares with t outside [0, 1] and says nothing about TD.
- **Refuter.** Not run (scratch; another refuter is checking TD's data).
- **Literature.** Not searched.
- **Metric.** A11: unchanged.
- **Meaning.** B53's strong lemma fails on TD as on L35 (O20), so A11 cannot cross its breakpoints locally either; its single strategy for p ≤ 6 steers around the flips. TD's remaining advantages are its explicit base (mirror at t → 0+) and few interior near ties.

### 2026-10-28: TD's single strategy leaves partner play without a simple rule (A11)

- **Claim / question.** A11's base is mirror play (answer with the partner). Is TD's single strategy over all t "partner, except under a short condition"? A short condition would be a describable drawing strategy for {1..2p}.
- **Approach.** `scratch/a11/tdstrat.rs` (the cell engine plus a walk of Z's strategy over all cells, preferring the partner of the opponent's last pick, else the smallest drawing number); fam a, p = 2, 4, 6. Features at every decision where the partner is available (`tdfeat-a-*.csv`): uppers held by each player, kind and rank of the opponent's pick, intact pairs, the lead's t-part and integer part, numbers left; search over single thresholds and pairs of them for a condition covering every partner failure.
- **Outcome.** p = 6: one strategy for all of (0, 1] in both roles (P1 needs the exact twins point t = 0 apart); P2's walk: partner 6,370, deviations from an available partner 472 (5%), own-turn continuations 1,066, no partner 1,001. Deviations look like token management (Z stops taking upper elements once it holds p/2 of them), but failures spread over many feature cells with 10–40% failure each; the best one or two thresholds covering all failures also flag 5,246 of 6,370 good partner answers. At p = 4, 28 of 416.
- **Refuter.** Not run (negative; the cell engine is with the refuter).
- **Literature.** Not searched.
- **Metric.** A11: unchanged (pieces 1 for p ≤ 6).
- **Meaning.** TD's single strategy exists but, like L35's, is not "mirror plus a short exception": the exceptions depend on the exact integer lead, which is the low phase's change-making again.

### 2026-10-28: bounded margin rows are not kept by optimal play (A2, A4)

- **Claim / question.** Interval margin rows take only the values 0, ±1 at every deficit d ≤ N (N ≥ 6). Is F = {S : |m(S, d)| ≤ 1 for every d ≤ max S}, where the value is fixed by parity alone, a family closed under optimal play (a margin form of A2's invariant region)?
- **Approach.** `scratch/a10/bounded.rs`: margin table on {1..16}; F by holes below max S; for every S ∈ F and d ≤ max S, whether some or every value-keeping pick leads into F.
- **Outcome.** Every interval {1..N} with N ≠ 5 is in F (to 16). F by holes: 15/16, 87/120, 369/560, 977/1,820, 1,549/4,368, …, 11/11,440 at 8 holes, none beyond. Of 81,680 positions (S ∈ F, d ≤ max S), some optimal pick stays in F at 64,149 (79%), every optimal pick at 8,933.
- **Refuter.** Not run (negative).
- **Literature.** Not searched.
- **Metric.** None (A2, A4 shelved).
- **Meaning.** The margin form of "dense sets draw by parity" fails closure as O5 does for holes: at a fifth of the family's positions optimal play must leave it. Margins sharpen the far-block picture (L34) but give no invariant for the low phase.

### 2026-10-28: pairing defenders lose by a margin growing with N (A3, new angle)

- **Claim / question.** A quantitative relaxation of L1: does an explicit pairing defender keep the final margin above a constant −C for every N? Then "the loser loses by at most C" would be a provable-looking partial theorem with the gap to the draw isolated. O6 says forced partner replies lose; by how much?
- **Approach.** `scratch/a10/pairmargin.rs`: margin game on {1..N}, even totals N ≤ 20; when the attacker's turn ends on y and y's partner is left, the defender's next turn starts with it; its other picks are optimal (best margin); pairs aligned {2j−1, 2j} or from the top {N, N−1}, {N−2, N−3}, ….
- **Outcome.** Aligned pairs: D as P2 loses by 2, 0, 6, 2, 10, 4, 14, 6 at N = 3, 4, 7, 8, 11, 12, 15, 16 (as P1 0, 0, 2, 2, 4, 4, 8, 4). Pairs from the top: 0, 0, 2, 2, 2, 4, 4, 4–6, 6, 6–8 at N = 3..20 (both roles). Free game: 0 throughout.
- **Refuter.** Not run (negative; the free game reproduces the known draws).
- **Literature.** Not searched.
- **Metric.** None.
- **Meaning.** Forced partner replies cost about N/3 even with otherwise perfect play, so a bounded-loss theorem cannot come from pairing; any explicit strategy with bounded loss must already make change in the low phase, the core difficulty itself.

### 2026-10-28: simple partner rules lose TD already just above t = 0 (A11, B61)

- **Claim / question.** A11's base: is there an explicit rule, partner answers plus a fixed choice when the defender is free, that draws TD in its first cell t ∈ (0, 1/(p + 1)) (where every t gives the same game), and how far up in t does it hold?
- **Approach.** `scratch/a11/tdrule.rs`: D follows a rule, the attacker is perfect, every cell of [0, 1] (breakpoints r/s, s ≤ p + 1, and midpoints); rules: partner of the attacker's turn-ending pick, else the smallest left (ps), the largest left (pl), or the smallest upper element left (pu); fam a, p = 2, 3, 4, both roles.
- **Outcome.** ps loses at every t > 0 in both roles from p = 2 (draws only at t = 0); pl draws only for p = 2 as P2 (all t) and fails in the first cell for P1; pu draws all t at p = 2, but at p = 3 it loses in the first cell as P1 and from t = 5/12 as P2, and at p = 4 in the first cell in both roles.
- **Refuter.** Not run (negative).
- **Literature.** Not searched.
- **Metric.** A11: no explicit base strategy beyond t = 0.
- **Meaning.** Exact twins draw by a recursive mirror on the top pair (the twins fact of 2026-10-22), not by answering every pick with its partner; at t > 0 an infinitesimal tie-break on upper elements adds a token game. A11's base is therefore itself a lemma to prove, "twins with an infinitesimal tie-break draw" (the first cell), before any crossing.

### 2026-10-28: TD's first cell draws to p = 11; twins with a tie-break fail on sparse bases (A11)

- **Claim / question.** A11's base as a lemma: do pairs {x, x + t}, t infinitesimal (first cell), draw with the mover trailing by t·(|B| mod 2), for TD's bases (odd or even numbers) and for every base set B?
- **Approach.** `scratch/a11/twineps.rs`: t = 1/(2|B| + 2) (t-parts never outweigh an integer), memoized solver; every B ⊆ {1..14} with |B| ≤ 6; TD's bases to the largest p that runs in a minute.
- **Outcome.** TD: draw for fam a p ≤ 11 (31M states, 35 s) and fam b p ≤ 10. General B: draw for all |B| ≤ 4; 3 of 2,002 fail at |B| = 5 and 9 of 3,003 at |B| = 6, all with a sparse high core ({7,8,10,11,12} and {7,8,10,11,13}: mover loses; adding 1, 2 or 3 below gives a mover win).
- **Refuter.** Not run (the TD data is with a refuter; this extends it in one cell only).
- **Literature.** Not searched.
- **Metric.** A11: the base cell holds to p = 11 (full range to p = 8, unchecked).
- **Meaning.** The base of A11 is a lemma about twins with an infinitesimal tie-break; it is not true for all bases, so like L35 (O19) it must use the structure of the odd or even numbers.

### 2026-10-28: a pairing leader loses L31's one-sided starts too (A3, L31)

- **Claim / question.** L31(b) needs only one role, the leader one point ahead on {2..N} and on {3..N}, not to lose. Does a pairing leader (forced partner replies, otherwise perfect) manage that, where pairing failed for the full draw (log 2026-10-28: pairing defenders lose by a margin growing with N)?
- **Approach.** `scratch/a10/pairmargin.rs` with an `l31` mode (set {lo..N}, the mover trailing by 1, D the leader); pairs aligned or from the top ({N, N−1}, …, the natural pairing of these sets). A first run added the starting lead twice (the free game showed +1); fixed, the free game now gives 0 at both starts for every N, as known.
- **Outcome.** Pairs from the top: the leader's final margin on {2..N} / {3..N} is −2/0 (N = 4), −2/−2 (7), −2/0 (8), −4/−4 (11, 12), −6/−6 (15), −4/−6 (16), −8/−6 (19), −6/−8 (20). Aligned pairs are worse (to −18 at N = 19).
- **Refuter.** Not run (negative; the free game reproduces L29's draws).
- **Literature.** Not searched.
- **Metric.** None.
- **Meaning.** One-sidedness does not rescue pairing: a leader must make change in the low phase just as a drawing player must.

### 2026-10-28: TD's data survives the refuter to p = 10; its mirror base does not (A11)

- **Claim / question.** The refuter on A11's evidence: TD draws for every t ∈ [0, 1]; one strategy for all t up to p = 6 and the piece counts at p = 7, 8; the sketch that mirror play reduces t → 0+ to Catch-Up on unit tokens.
- **Approach.** Refuter, claim mode (`scratch/refuter/td/`): `tdref.rs` over intervals of t (asserting that no comparison changes sign inside a gap between fractions with denominator ≤ p + 1), a second engine on breakpoints, thirds of gaps and t = 10⁻⁶ … 1 − 10⁻⁶, and `tdlex.rs` for the exact t → 0+ limit; controls: A278587 to N = 16, O7, O9, O13, O17's counts for p = 3, 4, 5.
- **Outcome.** Claim 1 SURVIVES and extends: draw at every t for both families, p ≤ 10; the bound s ≤ p + 1 is exact (largest t-coefficient p + 1 for odd p, p for even p). Claim 2 SURVIVES for the counts, but split points are artefacts of the greedy search's direction: fam a p = 8 searched upward gives one strategy on (0, 1) and t = 1 apart; the same holds for O17 (corrected there). In the cases that feed L1 (fam a with p even, fam b with p odd) the fewest pieces are 1 for p ≤ 7, 1 for fam b to p = 10, 2 for fam a at p = 8 and 10 (split near 2/3 at p = 10); the 3-piece cases are side cases. Claim 3 is BROKEN as a mechanism: completing the opponent's broken pair loses (8 rules, from p = 3 as P1, p = 4 as P2; e.g. fam a p = 2, P1 opening 3 + t loses by 2), and the limit game differs from unit-token Catch-Up at other deficits (fam a p = 2 at deficit ε; fam b p = 5 at a tie; 363 of 1,540 small cases), agreeing only at TD's own deficit.
- **Refuter.** Split: claims 1, 2 SURVIVE (with the reading of split points corrected); claim 3 BROKEN.
- **Literature.** Refuter: A278587 opened; two searches, nothing on twins, deformations or mirror strategies for Catch-Up; no proof announced.
- **Metric.** A11: pieces in the relevant cases 1 for p ≤ 7 (both families) and fam b p ≤ 10; 2 for fam a p = 8, 10; data to p = 10.
- **Meaning.** TD is solid as data and its strategies are nearly uniform in t, but its easy end is not easy: the first cell needs its own proof (no mirror, no token reduction). O17's claim that blocks need a strategy per integer band was an artefact of the search; only its counts stand.

### 2026-10-28: L36's drawing play opens the smallest pair, then uppers (A11, L36)

- **Claim / question.** How do players draw TD's first cell (L36)? Which openings and replies keep the draw, and how is the count of upper elements handled?
- **Approach.** `scratch/a11/cellplay.rs`: the lexicographic game (values x·K + s, K = 2p + 2), every drawing move along drawing lines to a given depth; fam a p = 4, 6; fam b p = 5.
- **Outcome.** Fam a (p = 4, 6): P1's only drawing openings are 1 and 1 + ε; P2's only drawing reply completes the pair; the player then behind by ε must open with an upper element of a middle pair (3 + ε or 5 + ε; never the smallest intact pair, never the top). Later decisions of a player behind by exactly ε are mostly the top upper element (11 + ε in 16 of 30 cases at p = 6). Fam b p = 5 (mover trailing by ε): many drawing moves at every node (P1: 2, 2 + ε, 4 + ε; P2's replies to 2: 2 + ε, 4, 6, 8, 10 + ε).
- **Refuter.** Not run (descriptive, scratch).
- **Literature.** Not searched.
- **Metric.** A11: unchanged.
- **Meaning.** The first cell's play has a visible start (smallest pair, then an upper in the middle) but no uniform rule for the ε-behind player; fam b leaves wide choice. Not yet a proof idea for L36.

### 2026-10-28: RPG survives only with grabs bounded as at c = 0; the quadruple negatives were overstated (A10, B60)

- **Claim / question.** B60: the refuter on the ideator's RPG (the moving top pair: D reserves {n − 1, n}; when O takes one, D's next turn ends with the other after grabs that keep D behind), its claim that the game tree does not depend on c, its margins, and the negatives for the quadruple, nested pairs and close-at-once (log entry "ideator on the low phase").
- **Approach.** Refuter, claim mode, own turn-level engine reproducing A278587 for n = 3..20 (`scratch/refuter/rpg/`), c swept over integers to 1000, sixths, and halves; the ideator's codes re-implemented.
- **Outcome.** With "stay behind" read at the actual c the tree does depend on c: n = 6, D as P1: −1 at c = 0, +1 for every c > 0 tested; n = 9, 10, 13 change too (odd totals only; even totals never changed to n = 16). With grabs bounded as at c = 0 (grab total < a − d_O, as coded) the value is constant in c, D always has a legal move, and RPG meets the margin target in both roles for n ≤ 23 (0 at even totals, −1 at odd, except n = 5 as P1). Then L1(n) ⇐ RPG_∞(n) is valid but says nothing new: RPG_∞ and RPG_0 are the same tree. Quadruple: the −2 at N = 11 needs an unstated clause (D's lead after closing below the smallest quadruple number); as stated N = 11 draws, N = 12 fails only for c ≤ 1, N = 15, 16 fail at every c. With the literal grab rule D draws N = 15 (c ≥ 1) and 16 (c ≥ 2). `gtc.rs` checks grab-then-close, not close-at-once; true close-at-once on the top 2 pairs fails at n = 8, 12. Nested pairs and compat confirmed exactly.
- **Refuter.** Claim 1 BROKEN as worded, SURVIVES as coded; claim 2 SURVIVES (n ≤ 23); claim 3 mostly confirmed, two details wrong (above).
- **Literature.** Refuter: A278587 opened and reproduced; three searches, no proof, nothing on reserved-pair or deformation strategies.
- **Metric.** A10: unchanged (shelved).
- **Meaning.** Corrects the entry "ideator on the low phase": only about four restricted rules were tested, so "no restriction makes the quadruple's tree c-independent" is too strong; the tested ones fail, L35's c-uniform strategy remains undescribed. The top pair can be reserved exactly, which reduces nothing.

### 2026-10-28: stall ideator: a universal gap bound implies L1 (new A12)

- **Claim / question.** Review after 107 entries, the problem stalled: ideas that could move the core difficulty, or a reachable weaker theorem.
- **Approach.** Ideator (effort max), `scratch/ideator/stall28/`; everything unchecked; its solver reproduces the signs of [results/values-n1-31.md](results/values-n1-31.md) for N = 1..22. My reproduction: `scratch/a12/lgcheck.rs` (own margin table).
- **Outcome.** (1) LG (L37): m(S, d) ≥ −γ(S ⊎ {d}) for every multiset S and d, γ the largest gap of sorted S ⊎ {d} ∪ {0}; its tie form G (|m(S, 0)| ≤ γ(S)) is equivalent over multisets and gives L1 at intervals (γ = 1, parity, L33). No violation in about 140M positions (every S ⊆ {1..22}, d ≤ 22; multisets; random values to 1000; generic ties to 10⁶; O7's cores; O2, O3, O10, O15); tight exactly at odd-total intervals ({1..9}, {1..10}, {1..14}, {1..18} lose by 1), their doubles and {2, 4, …, 16, 17, 19}. Mine: 0 violations on every S ⊆ {1..20}, d ≤ 20 (22.0M positions), G at every tie, interval margins ±1 at odd totals to N = 20. The two-ply induction fails at intervals by construction; a proof needs an amortized potential. (2) L38, a margin two-token lemma with a short copying proof: A(S, t) + A(S, y) ≥ 0 for openings y ≠ t, so G at S needs only two distinct safe openings (all 10M opening pairs within {1..18}). (3) LG over the reals in small cases as a diagnostic (B65); (4) the potential search (B64). Dropped with data: simple strategies with bounded loss (smallest ≥ deficit, nearest, smallest: lose by about N; always-max by N/2), gap-greedy play (−10 at N = 11, 12), local refinements of LG (675 violations within {1..14}), small move menus for LG-safe moves (miss 3,194 and 519 positions within {1..16}). Its advice: do not shelve yet; 3–4 units on LG, shelve if it breaks or no potential closes; bank the Lean results now either way.
- **Refuter.** Not run yet (next: claim mode on L37, proof mode on L38 and the reductions).
- **Literature.** Ideator: two searches on Catch-Up (nothing new), arXiv 2005.06326 (cumulative games, nothing on this), adversarial number partitioning (nothing on this game); the max-gap bound for greedy partitioning is its own derivation.
- **Metric.** New line A12: L37 checked to every S ⊆ {1..22} (ideator), {1..20} (mine).
- **Meaning.** The first statement on the table that needs no family closed under play: a bound at every position, tight exactly at the intervals. Its open part is a potential, the kind of object that worked for high sets (W, L23).

### 2026-10-28: two potential templates for LG fail exactly at intervals (A12, B64)

- **Claim / question.** B64: does LG (L37) follow by induction from a simple potential? Two templates: (1) the gap itself, Φ = γ(S ⊎ {d}), as the trailer's lower potential, with the least upper potential Ψ* it allows (the mover's best when every hand-over is valued at the opponent's guarantee −Φ); (2) measuring only at ties: from a tie on S, the player to move (lower half) or the other (upper half) steers so that the next tie S' has γ(S') ≤ γ(S), or the game ends within γ(S).
- **Approach.** `scratch/a12/lgcheck.rs` (also: two-sided LG, and a one-player step keeping γ), `potcheck.rs` (Φ = γ against condition (L): some move to a child with Φ no higher, or a hand-over with Ψ* no higher), `tietie.rs` (tie-to-tie DP with the threshold as a state); all sets S ⊆ {1..12} or {1..14}, deficits to 20–26; the exact potential −m passes `potcheck` as a control.
- **Outcome.** Two-sided LG is false (S = {1, 3}, d = 2: the mover wins by 2 > γ = 1, taking 1 then 3), and a pick keeping the gap need not exist (S = {2, 3}, d = 1). (1) Φ = γ is a valid bound (never below the true loss) but not self-supporting: (L) fails at 14,736 of 106,470 positions, among them {1, 2, 3, 4} at a tie; there γ overstates a child's loss (({3, 4}, 1): γ = 2, true loss 0). (2) Tie to tie fails at 127 (lower half) and 186 (upper half) of 4,095 tie roots within {1..12}, among them {1..7}.
- **Refuter.** Not run (negative; the control passes).
- **Literature.** Not searched.
- **Metric.** A12: two of B64's templates fail.
- **Meaning.** Intervals are LG's tight case and both templates break exactly there: a potential must value the small remainders exactly (as L7 does for two numbers), not by gaps. One template left in B64 (depth-weighted holes as in L23, or greedy-partition invariants); A12 meets its kill criterion if it fails too.

### 2026-10-28: exact endgames do not make the gap potential inductive (A12, B64)

- **Claim / question.** B64's third template: Φ_k = the exact loss when at most k numbers are left (provable endgames: L7 for k ≤ 2, Feng's thesis for 3–4), the gap γ(S ⊎ {d}) above. Does some small k make condition (L) hold everywhere?
- **Approach.** `scratch/a12/potcheck.rs` with Φ = hybK, k = 2..6, all S ⊆ {1..12}, d ≤ 25.
- **Outcome.** Valid everywhere, never self-supporting: (L) fails at 10,459 / 6,805 / 3,634 / 1,377 / 342 positions for k = 2..6, and every k first fails at the interval with k + 3 numbers ({1..9} at d = 3, 5, 7 for k = 6). After the trailer's move from an interval, the opponent's positions are intervals with one hole, where γ = 2 overstates the loss.
- **Refuter.** Not run (negative).
- **Literature.** Not searched.
- **Metric.** A12: B64's three templates fail; A12's kill criterion is met (L37 itself stands, refuter running).
- **Meaning.** Any potential built on gaps must value near-intervals exactly at the step from {1..n}, and their children have more holes (O5): the induction for LG at intervals carries the whole low phase. LG remains a clean conjecture (the loser never loses by more than the largest gap), with intervals as its tight case, but gives no proof route without a new idea for that step.

### 2026-10-28: no simple move rule meets LG even on generic positions (A12, B65)

- **Claim / question.** B65, light: on generic positions (no accidental ties), is some simple move always LG-safe (value ≥ −γ(S ⊎ {d}))? If so, LG's difficulty would sit in degenerate positions such as intervals.
- **Approach.** `scratch/a12/lggeneric.rs`: 20,000 random positions, |S| = 3..7, values up to 10⁶, d up to 1.2·10⁶ (seed 7); exact margin by memoized search; rules: min, max, smallest x ≥ d, largest x < d (else smallest ≥ d), nearest to d, least overshoot.
- **Outcome.** LG holds at all 20,000 and every position has a safe move. Every rule fails somewhere: largest below d 1.6%, min 2.4%, nearest 5.6%, smallest ≥ d and least overshoot 10.3%, max 13.8%.
- **Refuter.** Not run (negative).
- **Literature.** Not searched.
- **Metric.** A12: unchanged (kill criterion already met).
- **Meaning.** LG has no one-rule mechanism even in general position; its safe moves depend on the whole position, as the low phase's do. B65's full cell analysis is not worth running.

### 2026-10-28: the sign lemma, the margin two-token lemma and LG's reductions survive proof mode (A12)

- **Claim / question.** Proof mode on L33 (V = sign(m)), L38 (A(S, t) + A(S, y) ≥ 0 for openings of distinct values, with consequences (i), (ii)) and L37's reductions ((1) LG ⇒ G, (2) G ⇒ LG on multisets, (3) G({1..N}) ⇒ L1).
- **Approach.** Refuter, proof mode (`scratch/refuter/l38/`): case lists; a line-by-line Python port of `valueAux` (flag, early loss, scores) against sign(m) on every subset of {0..11}, g from −2 to sum + 3; multisets over {1..6} and {1..8}; all S ⊆ {1..18} for L38 and G; 20,000 random sets and multisets.
- **Outcome.** All SURVIVE, with wording fixes applied in the blueprint: L33 now mentions the opening flag and multisets; L37 states γ(∅) = 0 and treats d = 0 in (2) separately. A limit: L38 (ii)'s hypothesis (two distinct safe openings) fails on some multisets with repeats where G still holds ({2, 2, 5, 5}: γ = 3, A(2) = 0, A(5) = 4; 12 multisets over {1..8}), so G on multisets cannot come from (ii) alone; no set without repeats lacks two safe openings (all within {1..18}, 20,000 random). The margin parity m ≡ sum + g (mod 2) holds over all plays.
- **Refuter.** Proof mode: L33 SURVIVES, L38 SURVIVES, L37's reductions SURVIVE.
- **Literature.** Refuter: two searches, only the README's sources; nothing on margins, gap bounds or a two-token argument; the MPRA PDF had no readable text.
- **Metric.** A12: L33, L38 to `paper proof`.
- **Meaning.** The frame of A12 is sound: L1 follows from L37 by checked arguments, and L38 halves the work at sets. The open part is L37 itself, whose potential route failed at intervals (log: exact endgames do not make the gap potential inductive).

### 2026-10-28: the gap bound survives the refuter on 80 billion positions (A12)

- **Claim / question.** The refuter in claim mode on L37 (LG: m(S, d) ≥ −γ(S ⊎ {d}) for every multiset S and d) and its tie form G, plus the ideator's evidence.
- **Approach.** Refuter (`scratch/refuter/lg/`): a parallel dense engine over all sub-multisets of a root and all deficits, matched against a naive solver (688K values), a sparse memo solver and a Python solver; signs reproduce A278587 (N = 3..20) and our table (21..27); targeted families and hill-climbing.
- **Outcome.** SURVIVES: 0 violations in about 80 billion positions (every S ⊆ {1..27}, d ≤ 27; high-multiplicity multisets; large deficits; one big gap between dense parts; O10 translated and doubled; O7's whole five-pair family and its sub-positions; two-scale compositions; perturbations of tight cases; hill-climbing: distinct-value sets peak at ratio 0.974; generic values to 10⁶). Intervals: |m| = 1 at odd totals N = 21, 22, 25, 26, m = 0 at 23, 24, 27, and m({1..N}, d) ≥ −1 for every d ≤ N ≤ 27. Corrections: ({a, b, a + b}, d = a) is tight only when a < b ≤ 2a; the ideator's O7-core check never ran as described, and its generic-tie check tested only G's lower half; the refuter covered both.
- **Refuter.** Claim mode: SURVIVES.
- **Literature.** Refuter: A278587 and Eastaway's blog opened (signs and cases only); searches on margins of victory in Catch-Up, adversarial differencing or partitioning games with a gap bound, and 2026 proofs found nothing.
- **Metric.** A12: L37 checked on every S ⊆ {1..27} and ~80G positions.
- **Meaning.** L37 is as solid a conjecture as computation can make it, it implies L1 by checked arguments (L33, L37's reductions), and it is tight exactly at the intervals; what it lacks is a proof, and the gap-based potentials fail there.

### 2026-10-28: an upper companion to LG holds, but cannot close the induction (A12)

- **Claim / question.** LG's induction failed because the opponent's side was valued too pessimistically. Is there a natural two-sided bound to pair with it? Candidate: m(S, d) ≤ max(γ(S ⊎ {d}), sum(S) − d) (a trailer gains beyond a gap only by collecting small numbers).
- **Approach.** `scratch/a12/lgcheck.rs`, every S ⊆ {1..14}, d ≤ 20.
- **Outcome.** No violation (the plain two-sided form m ≤ γ fails, e.g. {1, 3} at d = 2 wins by 2). It cannot rescue Φ = γ: `potcheck.rs` already used the least upper potential Ψ* that Φ allows, and any valid upper bound is at least Ψ*, so condition (L) fails at least where it did.
- **Refuter.** Not run (a side fact; no use for it yet).
- **Literature.** Not searched.
- **Metric.** None.
- **Meaning.** The obstacle is the lower potential at intervals, not the upper side.

### 2026-10-28: drawn play in L36 balances upper elements, not pairs (A11, L36)

- **Claim / question.** Is L36's drawing play "every pair split, plus a game for the upper elements"? Then L36 would reduce to a mirror on the integer level and a token game.
- **Approach.** `scratch/a11/cellsplit.rs`: every drawing line of TD's first cell (both players keep the draw at every pick), end positions by unsplit pairs and by upper elements held; fam a and b, p = 2..8.
- **Outcome.** Upper elements always end (⌈p/2⌉, ⌊p/2⌋) for (P1, P2), as a draw at generic ε requires. Pairs need not be split: all drawn lines split every pair only for fam a p ≤ 4 and fam b p = 2; from fam a p = 5 and fam b p = 3, drawn lines also end with 3–8 pairs taken whole by one player, balanced on the integer level (fam a p = 8: 120 all-split ends, 286 with 4 unsplit, 22 with 6; fam b p = 8: 140 all-split of 1,732).
- **Refuter.** Not run (descriptive).
- **Literature.** Not searched.
- **Metric.** A11: unchanged.
- **Meaning.** Drawing lines with every pair split always exist, but the opponent can steer into lines with whole pairs; L36 is not "mirror plus tokens" (consistent with the refuter's breaking of the mirror base).

### 2026-10-28: review ideator: no idea gets past the step from an interval (A12, A7, A11)

- **Claim / question.** Review after 120 entries: any idea for the step from an interval without a closed family and without a gap potential; or a recommendation to shelve.
- **Approach.** Ideator (effort max), `scratch/ideator/interval28/`; unchecked; its engine reproduces A278587 for N ≤ 20.
- **Outcome.** No route. (1) Candidate O21 (paper, refuter pending): at (∅, g) the mover loses exactly g, so any potential f(γ) has f(g) ≥ g; every opening of {1..N} has a reply leaving γ ≥ 2 (after opening 1, every reply does), so f(γ) cannot certify the step from an interval, for any f; adding parity and count does not help (2·{1..10} loses by 2 with γ = 2, an even total and 10 numbers). Data (`depth2gap.rs`): the attacker spends the bottom run {1..k} as change, leaving the opener a non-losing block with holes and γ = k + 1, up to 6 at N = 20 (about √(2N)); e.g. N = 20, opening 20, reply {1..5, 19}, deficit 14, m = 0. So the interval step contains A7's open descent (blocks with holes at low height). (2) Tie rules do not matter: LG holds with adversarial or reversed exact catch-ups on every S ⊆ {1..20}, d ≤ 20, and even-total intervals and twins draw under all four tie rules (`tierule.rs`, `twinties.rs`). (3) The unsigned variant (one player minimizes |margin|) fails at intervals (2–6 by N = 20), so AtCoder AGC056 D's closed-form method does not carry over. (4) A new inequality A(S, 1) + A(S, 2) ≤ 2γ(S) on all 262,144 sets ⊆ {1..20} containing 1 and 2 (tight at {1, 2, k} and odd-total intervals); with L38 it gives "P1 does not lose" at even-total intervals given the bound, but its proof reduces to blocks with a hole at height 3; no fixed pair of openings works (111 failures for the two smallest within {1..16}). Ideas kept: record O21; B44 as the first rung every route needs (a rule "Hyb3" with a W-type potential for blocks at heights [p + 2, 2p − 2], about 10% for a new block theorem, below 1% toward L1); L36 as a token game on a fixed tree (about 2%). Recommendation: bank the Lean block theorems and a note on L37 (with L33, L38, the reductions), then shelve L1.
- **Refuter.** Not run yet (proof mode on O21 next).
- **Literature.** Ideator: Catch-Up proofs, arXiv 2025–2026, von Stengel's talk, trailer-picks games with gap bounds: only known sources; the AtCoder AGC056 D editorial opened (an alternating |X| game with a joint-induction closed form, same shape as L14, L20; does not transfer); arXiv 1808.06922 is a different "catch-up" rule.
- **Metric.** A12: none (route closed). A7: B44 promoted.
- **Meaning.** Every route meets the same object, blocks with holes at low height after a change-making reply; no potential that only reads gaps can see it. The honest options are banking and shelving, with B44 the one concrete theorem-level item left.

### 2026-10-28: below Hyb2's height the block strategy has no short amendment (A7, B44)

- **Claim / question.** B44, the first rung every route needs (review ideator): on blocks {h..h+2p−1} at debt p mod 2 with h in [p + 2.2, 4p], where does the one strategy for all heights leave Hyb2, and is the difference a short rule ("Hyb3")? Test as planned: at most three describable differences that keep every block drawn → a W-type potential next; otherwise shelve A7's descent.
- **Approach.** `scratch/a7/b44.rs` (the ideator's universal-strategy search over 24–32 generic heights, plus a walk preferring Hyb2's pick); `scratch/a7/hyb3.rs` (rules as full strategies against a perfect opponent at every integer height p + 2..2p + 2, p ≤ 7): Hyb2, and Hyb2 amended to take the smallest number when continuing its own turn, when no pick meets the matching cost, or after a two-pick reply.
- **Outcome.** One strategy covers every sampled height in both roles for p = 4, 5, 6. It leaves Hyb2 at 5 / 3 decisions (p = 4, P1 / P2), 9 / 13 (p = 5), 78 / 100 (p = 6) of a few thousand (1–2%); Hyb2's pick never depends on h; most deviations take the smallest number with a small lead where Hyb2 demands a lead of at least the matching cost (p = 5, a = 8, after 17 | 9, 13: the strategy takes 8 with lead 2, Hyb2 takes 11 with lead 5), and at p = 6 P1 opens offset 7 instead of 11. Hyb2 as a full rule loses exactly at a < 2p − 1 (p = 7: a = 9..12), reproducing L24's tightness. All three amendments lose at every height tested, high ones included.
- **Refuter.** Not run (negative; Hyb2's baseline reproduces L24).
- **Literature.** Not searched.
- **Metric.** A7: the descent below 2p − 1 has no short rule; B44's test fails.
- **Meaning.** The block strategy below Hyb2's height needs a refined cost condition that grows with p, the change-making of the low phase again; as planned, A7's descent is shelved at the next review.

### 2026-10-28: no literature on differencing games with a catch-up turn rule (A12, literature)

- **Claim / question.** Catch-Up as differencing (a pick x replaces the deficit d and x by |d − x|) is the Karmarkar–Karp step restricted to the current deficit. Is there theory on two-player or adversarial differencing / partitioning games, ideally with a bound on the final discrepancy in terms of gaps, that could prove L37?
- **Approach.** Web searches: adversarial or two-player Karmarkar–Karp differencing with a gap bound; two-player number partitioning where numbers go to the lighter side; picking games where the player behind moves until ahead. Opened arXiv 1803.02621.
- **Outcome.** Nothing on such a game. Results cover one-player partitioning (Karmarkar–Karp differencing, LDM/PDM, random-instance analyses: arXiv 2103.01369, 2505.20607, 2309.15115), the Balancer–Unbalancer discrepancy game (Wikipedia, a different game), arXiv 2504.16752 (a leader–follower knapsack game, different), and arXiv 1803.02621 (CUT partition games: heap splitting under normal play, unrelated). The greedy "largest to the lighter side" heuristic is known as a one-player method only.
- **Refuter.** Not run (literature).
- **Literature.** As above; nothing usable.
- **Metric.** None.
- **Meaning.** L37's game version appears to be unstudied; its proof would need new arguments.

### 2026-10-28: L36 is not a token game on a fixed tree (A11, L36)

- **Claim / question.** The review ideator's idea 3: in L36's first cell the integer level dominates, so both players keep the exact-twins game drawn, and the upper-element tokens only decide who moves after an integer tie. If the integer-drawing moves at every position are the same under every rule for an exact catch-up, L36 is a token game on one fixed tree.
- **Approach.** `scratch/a11/tietree.rs`: exact twins of TD's bases under four tie rules (the turn passes; the catcher moves on; player 1 or player 2 chooses); every position on drawing lines of any rule; drawing-move sets compared; fam a p ≤ 7, fam b p ≤ 6.
- **Outcome.** Twins draw under all four rules (as the ideator found), but the drawing-move sets differ at 10 of 54 positions (fam a p = 4), 72 / 286 (5), 526 / 1,264 (6), 2,722 / 5,140 (7), and in fam b from p = 2 (2,721 of 3,695 at p = 6). Example: fam a, left {3, 3, 5, 5, 7, 7, 9, 9, 11, 11} at a tie with P2 to move: drawing moves {3, 5, 9} (turn passes), {3, 5} (catcher moves on), {3, 5, 9, 11} (P2 chooses).
- **Refuter.** Not run (negative).
- **Literature.** Not searched.
- **Metric.** A11: unchanged.
- **Meaning.** In L36 the tokens and the integer play are entangled from p = 4; no reduction to a token game. The ideator's three ideas are now all tested.
