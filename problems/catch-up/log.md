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
