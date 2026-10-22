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
