# Catch-Up conjecture

Idea log, failures included. Nothing here is trusted until proven in `lean/`.

## Problem

Catch-Up (Isaksen, Ismail, Brams, Nealen 2015) on {1..N}: player 1 opens by taking one number; afterwards the mover keeps taking numbers while strictly behind, and the turn ends on the pick that catches up (≥). A mover who can't catch up even with everything left loses. When the numbers run out, the higher score wins.

**Conjecture:** if 1 + … + N is even (N ≡ 0, 3 mod 4), optimal play is a draw. Lean: `CatchUp.Conjecture` in `lean/CatchUp/Statement.lean`, ported from formal-conjectures `value_of_even_mul_succ_self_div_two`; reviewed and approved by the user 2026-10-22.

## Known

- Exhaustive search to N = 28: von Stengel, talk abstract, CGT Colloquium III, Lisbon 2019 ([ludicum.org/?p=4151](https://ludicum.org/?p=4151)). No paper, code or data found.
- OEIS [A278587](https://oeis.org/A278587): values for N = 3..20.
- Original paper ([MPRA 108784](https://mpra.ub.uni-muenchen.de/108784/)): proves only the parity facts; notes that even-sum sets in general need not draw (multiset {2,2,2,3,3}).
- Endgames with 3–4 numbers left, case analysis: K. C. G. Feng, honors thesis, College of Staten Island 2024 ([pdf](https://www.math.csi.cuny.edu/Undergraduate/HonorsTheses/2024-feng.pdf)).
- No proof or partial proof found (searched 2026-10-22).

## Our solver

`solver/` (Rust): mirrors Lean `valueAux` with a 2-bit memo table; cross-checked against an independent turn-based reference on all subsets of {1..8} and against A278587. N = 24 in 25 s, single core.

## Observations (N ≤ 24)

- Draw for every even-total N, matching the literature.
- Player 2 wins only at N = 9, 10, 14, 18; from N = 21 player 1 wins with opening 3 (N ≡ 1 mod 4) or 2 (N ≡ 2 mod 4).
- **Parity law** (easy to prove): both players together take everything left, so the final score difference ≡ gap + (sum of numbers left) (mod 2). A draw is only possible when the parities match; otherwise the position is a win or a loss. Hence every position's values alternate with the gap's parity.
- **Parity rule, empirical** (`solver/src/bin/row_stats.rs`, N ≤ 22): the most common rows are exactly "mover wins where a draw is impossible, draw where it is possible" (`WDWD…`/`DWDW…`, gap 0, 1, 2, …). Deviations cluster at gaps ≤ 2 and at the largest gaps. When does the rule hold exactly? A candidate characterization for a proof.
- **Every opening move draws for even-total N ≥ 12** (exceptions only below: N = 3 opening 2, N = 4 openings 3–4, N = 7 openings 5–7, N = 11 opening 10). Both drawing strategies are robust, so a simple description may exist.

## Next

1. Reproduce N = 25..28, then N = 31 (new; about 17 GB table). N = 32 needs a smaller encoding.

## Backlog

Proof-hunt ideas, most promising first; each iteration takes one, logs it and updates this list.

1. **Near-pair switches** (wild). Paper sketch, untested: for multisets, value(S ⊎ {x, x}) = value(S) if x ≥ max(S), since answering x with the other x restores the position (gaps never exceed max(S), so taking x always ends the turn); the solver accepts repeated numbers, so check this first. For a pair {x, x+1} above max(R), the same answer shifts the gap by ±1, the first taker choosing the sign. Test whether V(R ∪ {x, x+1}, g) (V = mover's value with R left at gap g) is a function of V(R, g−1), V(R, g), V(R, g+1) for all R ⊆ {1..20}, x > max(R). If so, {1..N} peels into pairs from the top: a position-level induction on intervals.
2. **Draw region of positions** (seed items "position structure" and "parity rule"). Set-level laws fail (Log), so a proof needs a class of positions (numbers left, gap) both players can stay in. From the layered tables (N ≤ 22): where exactly are even-parity positions draws? Start at the parity rule's deviations (gaps ≤ 2, largest gaps), then test closure: from each class position the mover has a turn into the class, and every turn leaves the opponent at least a draw.
3. **Richer density notion** (variation of the Log's best result). Completeness nearly characterizes even-sum draws; find what its 523 exceptions with max ≤ 30 lack (`quad_step 30` lists the first). Candidates: consecutive numbers differ by ≤ 2; every amount payable in two disjoint ways; S ⊇ {1..k} with k ≥ max(S)/2.
4. **Drawing strategies.** Test simple rules for player 2 and for player 1 against a perfect opponent (largest number that catches up; smallest; minimal overshoot; mirror x ↦ N+1−x); report the first N where each fails, then patch the best rules at their failure positions. Build a reusable evaluator (`strategy_eval.rs`) and keep a leaderboard here.
5. **Endgames.** Exact value formulas for ≤ 3 numbers left, as Lean lemmas; compare with Feng's case analysis (Known) first.

## Log

### 2026-10-22: induction by four fails, even for complete sets

- **Claim.** If S has even sum and is a draw, adding a balanced quadruple Q = {a < b < c < d}, a + d = b + c, above max(S) keeps it a draw. Q = the next four numbers is the step {1..N} → {1..N+4}, which with N = 0, 3 would prove the conjecture.
- **Experiment.** `solver/src/bin/quad_step.rs`: `cargo run --release -p catch-up --bin quad_step -- 30` (2 min, about 4 GB; output in `scratch/quad_step-30.md`). One layered table on {1..U} gives value(S) for every S ⊆ {1..U}: its gap-0 entry, since a gap-0 turn is one pick like the opening. Checked against `Solver` on all subsets of {1..10} and 100 random ones; every reported set re-solved with `Solver` and, up to 9 numbers, with `reference_value`. Identical output with the library at 740f565 and 4b1ce2b.
- **Outcome: false.**
  - Any S: smallest break {2,7,9,14} (draw) + {15,16,17,18} → player-1 win. At U = 30, 32,652 of 32.7M even-sum draws break (0.1%).
  - Complete S (each number ≤ 1 + the sum of the smaller ones, so every amount up to the total can be paid exactly; {1..N} is complete): no break for S ⊆ {1..24}; first break {1,2,4,8,15,17,18,20,25} + {26,27,28,29} → player-1 win (1 of 5.86M complete draws). Non-consecutive quadruples break sooner: {1,2,3,5,6,9,14,18} + {20,22,24,26} → player-1 win.
  - Side result: every complete even-sum S with max ≤ 21 is a draw. Up to max 30, 523 of 93.7M are not, all sparse: first {1,2,3,7,9,11,14,15,22} (player 1 wins by opening 2); all player-1 wins except one loss, {1,2,3,4,6,7,8,16,18,21,22,26,27,29,30}.
  - Literature (web search 2026-10-22): nothing on complete sets or quadruple steps.
- **Meaning.** Adding four numbers doesn't preserve draws, not even for complete sets, so the interval induction needs more than completeness. The breaks are sparse sets, often starting 1, 2, 4, 8 (guess: few ways to pay each amount; Backlog 3). Completeness is also lost after one move (taking 1 breaks it), so the invariant must be about positions (numbers left + gap), not starting sets.
