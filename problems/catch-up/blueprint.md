# Blueprint

Status and Approved: `CLAUDE.md`, Workflow.

| ID | Name | Statement | Uses | Line | Lean | Status | Approved |
|---|---|---|---|---|---|---|---|
| L1 | Main conjecture | On {1..N} with 1 + … + N even, optimal play is a draw | — | all | `CatchUp.Conjecture` (statement) | conjecture | 2026-10-22 |
| L2 | Every opening draws | For even-total N ≥ 12, every opening move of player 1 still leads to a draw; implies L1 for those N | — | A3 | — | conjecture | — |
| L3 | Parity law | If `valueAux R a b f = draw` (mover's score a, opponent's b), then a + b + sum(R) is even; so a draw needs the integer gap b − a ≡ sum left (mod 2), and value(S) = draw needs sum(S) even | — | A2 | `CatchUp.parity_law`, `CatchUp.even_sum_of_value_eq_draw` (`CatchUp/Parity.lean`) | formalized | — |
| L4 | Near-intervals draw | Every even-sum {1..m} ∖ H with H ⊆ {1..m−1} is a draw when m > m0(\|H\|), m0 = 0, 3, 6, 10, 13, 14, 17 for \|H\| = 0..6; generalizes L1 (H = ∅) | — | A2, A4 | — | conjecture | — |
| L6 | Best by membership | best(os) = win ⇔ win ∈ os; best(os) = draw ⇔ draw ∈ os ∧ win ∉ os; otherwise loss | — | A2 | `CatchUp.Outcome.best_eq_win_iff`, `_draw_iff`, `_loss_iff` (`CatchUp/Best.lean`) | formalized | — |
| L7 | Endgames with ≤ 2 numbers | With the mover trailing by g (scores s and s + g, not the opening): ∅ is a draw if g = 0, else a loss; {a} is a win if g < a, a draw if g = a, a loss if g > a; {a, b} with a < b: for g ≤ a compare g + a with b (win if <, draw if =, loss if >); for g > a compare g with a + b (win if <, draw if =, loss if >) | L6 | A2 | — | paper proof | — |
| L5 | Moderate gaps draw | For R = {1..m} ∖ H, H ⊆ {1..m−1}, \|H\| ≤ 2, and every gap g ≡ sum(R) (mod 2) with 5 ≤ g ≤ sum(R)/12, the mover's value is a draw | — | A2 | — | conjecture | — |

## L1 Main conjecture
**Proof.** Open.
**Evidence.** Every even-total N ≤ 35 is a draw ([results/](results/); N = 33–35 from one engine, unchecked).

## L2 Every opening draws
**Proof.** Open.
**Evidence.** Every opening draws for each even-total N with 12 ≤ N ≤ 35 ([results/](results/)); fails at N = 3, 4, 7, 11. A middle band of gaps around every opening gap draws too (log 2026-10-22: interval rows).

## L3 Parity law
**Statement.** For every finite R ⊆ ℕ, a, b ∈ ℕ and flag f: valueAux R a b f = draw ⇒ a + b + sum(R) is even. Stated with a + b, not the gap b − a, which ℕ subtraction truncates when the mover leads (R = {4,5,6}, a = 3, b = 0 is a draw with b ∸ a + 15 odd). A statement about plays ("final difference ≡ gap + sum left") is false: the can't-catch-up rule ends a game with numbers untaken (valueAux {1} 0 5 false = loss).
**Proof.** Strong induction on |R|, for all a, b, f.
- R = ∅: the value is draw only if a = b, and a + b = 2a.
- a + sum(R) < b: the value is loss.
- Otherwise the value is best(os), os listing for each x ∈ R either neg(valueAux (R ∖ x) b (a + x) false) or valueAux (R ∖ x) (a + x) b false (by f and whether a + x ≥ b). Each entry comes from `R.attach`, so carries x ∈ R; that gives |R ∖ x| < |R| and x + sum(R ∖ x) = sum(R).
  - (B) foldl step acc os = draw ⇒ acc = draw ∨ draw ∈ os, by induction on os generalizing acc: step(acc, o) = draw only for (draw, loss), (draw, draw), (loss, draw). With acc = loss, best(os) = draw ⇒ draw ∈ os.
  - (N) neg(o) = draw ⇔ o = draw.
  - So for some x ∈ R a call on R ∖ x with scores a + x and b, in some order, is a draw. By induction a + x + b + sum(R ∖ x) is even, and x + sum(R ∖ x) = sum(R).

Corollary: value S = valueAux S 0 0 true, so value S = draw ⇒ sum(S) even.
**Evidence.** Independent port of `valueAux` (refuter, `scratch/refuter/l3/parity.mjs`): every R ⊆ {0..8}, a, b ≤ 20, both flags: 451,584 positions, 69,844 draws, no violation. Refuter (proof mode, 2026-10-22) on the first version: BROKEN (false play-level clause, proof about one play instead of the value); this version is its correction. Refuter (proof mode, 2026-10-22) on this version: SURVIVES (every case of `valueAux` audited; each proof step checked numerically on R ⊆ {0..9}, a, b ≤ 24, both flags, 1,280,000 positions). Known at the level of plays: the original paper (MPRA 108784, §2.6) notes that odd totals can't be split evenly.
**Lean.** `lake build --wfail` clean; `#print axioms`: propext, Classical.choice, Quot.sound. Deviations from the paper proof: (B) is proved for any step function with the property and then instantiated with `best`'s step (a generalization, checked case by case); the induction runs on n with `R.card = n`. Adapted from the refuter's scratch check (`scratch/refuter/l3v2/ParityCheck.lean`).

## L6 Best by membership
**Proof.** The step of the fold returns win if the accumulator or the element is win; else draw if either is draw; else loss. By induction on os, generalizing the accumulator acc: foldl step acc os = win ⇔ acc = win ∨ win ∈ os, and foldl step acc os = draw ⇔ (acc = draw ∨ draw ∈ os) ∧ acc ≠ win ∧ win ∉ os. With acc = loss this is the statement; the loss case is the remaining one, since best always returns one of the three.
**Evidence.** Refuter (proof mode, 2026-10-22): SURVIVES; the general-accumulator induction checked on every list of length ≤ 7 from every start (9,840 cases), including the arm order (only (draw, win) depends on it, and gives win).
**Lean.** `lake build --wfail` clean; axioms within propext, Classical.choice, Quot.sound. Deviations: the step is restated as a private `combine` (win if either is win, else draw if either is draw, else loss) and proved equal to `best`'s step case by case; the loss case is derived from the other two.

## L7 Endgames with ≤ 2 numbers
**Statement.** For s, g ∈ ℕ (mover's score s, opponent's s + g), isFirstMove = false: V(∅) = draw if g = 0, else loss. V({a}) = win if g < a, draw if g = a, loss if g > a. For a < b, V({a, b}) = (if g ≤ a: win if g + a < b, draw if g + a = b, loss if g + a > b; else win if g < a + b, draw if g = a + b, loss if g > a + b). Numbers may be 0. The mover-leading positions (scores s + g and s) are not covered.
**Proof.** By L6 the value is the best outcome over the picks.
- ∅: the scores decide: draw iff g = 0.
- {a}: if a < g the mover can't catch up (s + a < s + g): loss. Otherwise taking a ends the turn with the mover ahead by a − g and nothing left: win if a > g, draw if a = g.
- {a, b}, a < b, g > a + b: can't catch up: loss. Otherwise:
  - g ≤ a: a first ends the turn, and the opponent, trailing by a − g < b, takes b and wins: loss. b first (b > a ≥ g) ends the turn with the opponent trailing by b − g with {a}; negating the {a} case, the mover wins if g + a < b, draws if g + a = b, loses if g + a > b. That is the value.
  - g > a: a first leaves the mover trailing by g − a with {b}: win if g < a + b, draw if g = a + b. So g < a + b is a win. At g = a + b no pick wins: a first draws; b first either ends the turn (then b ≥ a + b forces a = 0, and the opponent, at gap 0 with {0}, ties) or leaves the mover trailing by a with {a}: a draw either way. So the value is draw.
**Evidence.** Refuter's literal `valueAux` port (`scratch/refuter/l7/`): every a < b ≤ 20, s ≤ 9, g ≤ a + b + 3 and the ∅, {a} cases, each set in ascending, descending and random move order: 104,050 positions, no violation. A first proof split "a < g ≤ b: win", false at a = 0, g = b (refuter, proof mode, 2026-10-22: BROKEN); this version is the repair. Refuter (proof mode, 2026-10-22) on the repair: SURVIVES (each step checked on a < b ≤ 25, s ≤ 6, 71,652 positions). Lean statement shape agreed: `valueAux ∅ s (s + g) false`, `valueAux {a} s (s + g) false`, `valueAux {a, b} s (s + g) false` with `a < b`, as `if` expressions without subtraction.

## L4 Near-intervals draw
**Proof.** Open.
**Evidence.** `near_intervals 30` (log 2026-10-22: near-intervals draw): no exception for 14 ≤ m ≤ 30, h ≤ 4 (71,204 sets at h = 4); the last exceptions are at m = 3, 6, 10, 13 for h = 1, 2, 3, 4. The same counts at m ≤ 22 from a second DP (`interval_rows`). Refuter (claim mode, 2026-10-22): SURVIVES; two independent engines reproduce every count; L4 also holds at m = 31 (refuter scratch). h = 5, 6 (log 2026-10-22: hole threshold): 296,912 and 1,018,103 sets, the last exceptions at m = 14 and 17, matching the refuter's engine.

## L5 Moderate gaps draw
**Proof.** Open.
**Evidence.** `near_intervals 30`: no exception for m ≤ 30 with gaps ≤ 30 (35,469 positions at h = 2). It fails with 3 holes (10 exceptions, last at m = 15) and 4 holes (131, last at m = 23), and fails badly for complete sets ({1,2,4,8,16} at g = 5 is a mover win). Refuter (claim mode, 2026-10-22): SURVIVES; its uncapped run covers the gaps 31 ≤ g ≤ sum/12 our run skipped for m = 27–30 (all draws); the first non-draw gap for h ≤ 2 lies at ≥ 1.17 · sum/12.
