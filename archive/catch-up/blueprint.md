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
| L8 | Pair sets draw | (E) S a union of p disjoint pairs {x, x+1} (every run of consecutive numbers has even length): V(S, p mod 2) = draw. (T) Same for {1,2,3} ∪ such a set above 3. Implies L1 | — | A5 | — | refuted (O7) | — |
| L10 | Reductions within L8 | (a) T = {1,2,3} ∪ E' (p pairs): V(T, p mod 2) ≥ neg V({2,3} ∪ E', (p+1) mod 2), so L8 (E) for {2,3} ∪ E' gives V(T, g0) ≥ draw. (b) E with p pairs, p even: if V(E ∖ P, 1) = draw for every pair P of E, then V(E, 0) ≤ draw | L6 | A5 | — | paper proof | — |
| L11 | Two pairs | V({a, a+1, b, b+1}, 0) = draw for all 1 ≤ a, b ≥ a + 2: L8 (E) at p = 2 | L6, L7, L10 | A5 | — | paper proof | — |
| L9 | Far-apart pairs | S = p pairs {a_i, a_i + 1} with a_1 ≥ p and each a_{i+1} > (sum of the pairs below) + a_i + 1: for 0 ≤ g ≤ a_1, V(S, g) = draw if g ≤ p and g ≡ p (mod 2), win if g < p and g ≢ p, loss if g > p. L8 (E) for these sets | L6 | A5 | — | paper proof | — |
| L12 | Even blocks draw | V({a..a+2p−1}, p mod 2) = draw for all a, p ≥ 1 (TI); a = 1 with p even is L1 for N ≡ 0 mod 4 | — | A7 | — | conjecture | — |
| L13 | High sets are the rounds game | For O a finite set of non-negative integers with \|O\| even, g ≥ 0 and a > g + sum(O): V({a + o : o ∈ O}, g) = R(O, g), where V(S, g) = `valueAux S s (s+g) false` (any s; the mover trails by g, not the opening) and R is the rounds game (section) | L6 | A7 | `CatchUp.valueAux_map_add`, rounds game `CatchUp.roundsValue` (`CatchUp/Rounds.lean`) | formalized | — |
| L14 | Greedy bound | T a set with \|T\| even, played out in \|T\|/2 rounds of one Z pick and one Y pick each, the order in each round and Y's picks chosen adaptively. If Z always takes the largest number left, Z's total − Y's total (picks from T only) is ≥ −c_td(T), c_td(T) = (t1 − t2) + (t3 − t4) + … for t1 > t2 > … | — | A7 | `CatchUp.neg_altSum_le_greedyWorst`, per round `CatchUp.altSum_round`, `CatchUp.altSum_top_two` (`CatchUp/AltSum.lean`) | formalized | — |
| L15 | Always-max on pair sets | In the rounds game on a pair set E (disjoint pairs {x, x+1}), a player Z who always takes the largest number left ends with final margin (Z's initial lead, negative when Z moves first, plus Z's picks minus Y's picks) ≥ −1 if Z starts as the mover trailing by 0 or 1, or as the non-mover leading by l ≥ 0 (l = 0: Y moves at a tie) | — | A7 | — | paper proof | — |
| L16 | High pair sets draw | For E a pair set with p pairs and a > 1 + sum(E): V({a + o : o ∈ E}, p mod 2) = draw. Gives L12 for blocks with a > 1 + p(2p−1), and L8 (E) for pair sets placed high | L13, L15 | A7 | blocks only: `CatchUp.block_draw_high` (`CatchUp/Blocks.lean`, via L23) | paper proof | — |
| L17 | Rows of high blocks | R({0..2p−1}, d) = t_p(d) for all d ≥ 0 (t_p: draw at d ≤ p with d ≡ p mod 2, win at d = 0 for p odd, loss otherwise); with L13, the row of {a..a+2p−1} for a > d + p(2p−1) | L13 | A7 | draw entries of blocks at a ≥ 6p − 2: `CatchUp.block_row_draw_linear` (`CatchUp/Linear.lean`) | conjecture | — |
| L18 | Catch-up potential step | T finite, \|T\| even, t1 > t2 > … the numbers left, c = c_td(T), c'' = c_td(T − {t1, t2}) (0 if \|T\| = 2). Z plays AM+T: first picker the largest left; second picker the largest left unless that gives an exact tie (margin 0 after the round, so Y keeps the move), then the second largest left (at \|T\| = 2 the only one). Γ = min(s + c, 0) if Z moves, max(s − c, 0) if Y moves, Γ = s at T = ∅. After one round Γ' ≥ Γ for every Y pick, unless Y moves with s < (t1 − t2) − c''; then exactly Y's pick t1 lowers it, to Γ − ((t1 − t2) − c'' − s) | L13, L14 | A7 | `CatchUp.potential_le_roundsMargin` (guarantee form) | formalized | — |
| L19 | Top-run lemma | E a pair set whose r largest pairs are adjacent ({m−2r+1..m} ⊆ E, the top run). In the rounds game with Z playing AM+T, from Z moving at debt d ≤ r or Y moving with Z leading by l ≥ 0, every round start where Y moves has s ≥ (t1 − t2) − c_td(T − {t1, t2}) when \|T\| ≥ 4 and s ≥ t1 − t2 − 1 when \|T\| = 2. With L18: Z's final margin ≥ −1 (≥ l − p − 1 for l > p); for E = {0..2p−1} (r = p) this is T1's floor | L18 | A7 | — | conjecture | — |
| L20 | Matching bound | O with \|O\| even, sorted o1 < o2 < …, c(O) = (o2 − o1) + (o4 − o3) + …. If d > c(O), R(O, d) = loss for the mover: the other player answers each pick with its partner in the matching {o1, o2}, {o3, o4}, … and wins by at least d − c(O) (R as in L13's section) | — | A7 | `CatchUp.roundsMargin_le_matchCost` (`CatchUp/Matching.lean`) | formalized | — |
| L21 | High pair sets at linear height | E a pair set with p ≥ 1 pairs, offsets ≥ 0, m = max E. If a > 3m: V({a + o : o ∈ E}, p mod 2) = draw. For blocks {a..a+2p−1}: a ≥ 6p − 2 (L16 needs a > 1 + p(2p−1)) | L15, L20, L22 | A7 | blocks only: `CatchUp.block_draw_linear` (`CatchUp/Linear.lean`, via L23) | paper proof | — |
| L22 | Strategy transfer | O with \|O\| even, offsets ≥ 0, a > max O, g ≥ 0; σ a strategy for Z (either role) in R(O, g) such that every round start reached in a play consistent with σ has debt < a. In the real game on {a + o : o ∈ O} at gap g, Z plays σ with the picks numbered from the start, picks 2k − 1 and 2k forming round k. Then every real-game play against σ is a rounds-game play against σ with the same picks and the same outcome; so Z secures in V at least σ's worst outcome in R | — | A7 | `CatchUp.valueAux_transfer` (`CatchUp/Transfer.lean`, draw threshold) | formalized | — |
| L23 | Depth invariant | Rounds game, Z plays AM+T. At a round start: T the numbers left, \|T\| = 2q, t1 > t2 > …; s Z's lead (Z moves if s < 0, Y if s > 0; at s = 0 the previous round's first picker, at the start the given mover); Hol(T) the integers strictly between min T and t1 not in T; D_Y(T) = Σ_{h ∈ Hol(T)} (t1 − h); D_Z(T) = Σ_{h ∈ Hol(T), h < t2} (t2 − h). K is the set of round starts with: T = ∅ and s ≥ −1; or T = {a > b} and s ≥ −(a − b + 1) if Z moves, s ≥ a − b − 1 if Y moves; or q ≥ 2, Z moves and (KZ) s + q ≥ D_Z(T); or q ≥ 2, Y moves and (KY) s + q ≥ D_Y(T), with s ≥ 1 if Hol(T) ≠ ∅. Every round from a K-state, whatever Y picks, ends in a K-state, so Z's final margin is ≥ −1. Z trailing by d ≤ p on {0..2p−1}, and Z leading by l ≥ 0 there with Y to move, are K-states | L13 | A7 | `CatchUp.depth_class_roundsMargin` (`CatchUp/Depth.lean`) | formalized | — |
| L24 | Blocks at the doubling-free height | For p ≥ 1 and a ≥ 2p − 1: V({a..a+2p−1}, p mod 2) = draw. Route: Hyb2 (Z answers with the smallest number leaving Y's debt ≥ c of what is left, else AM+T's answer: the largest, or on an exact tie the second largest; as first picker the largest). (a) Debt bound: along every rounds-game play against Hyb2 on {0..2p−1} from debt p mod 2 (both roles), every round start has debt ≤ 2p − 1 + min R (R the offsets left; L25) | L20, L22, L23, L25 | A7 | `CatchUp.block_draw_hyb2`, `CatchUp.block_row_draw_hyb2` (`CatchUp/Hyb2.lean`) | formalized | — |
| L25 | Hyb2's debt bound | Rounds game from {0..2p−1} at debt p mod 2, either player first, Z on Hyb2. The potential W (Ψ(R) = 2(max R − min R) − \|R\| + 2 − o₂(R), o₂ the second smallest; W = Ψ(R) at Z's round starts and at Y's with e < c(R), W = max(e − min R, min(e + c(R) − o₂, Ψ(R))) at Y's with e ≥ c(R)) never increases over a round and starts at 2p − 1. Hence every Y round start has e ≤ 2p − 1 + min R and every Z round start has d ≤ 2p − 1 | L20 | A7 | `CatchUp.potW_z_round`, `CatchUp.potW_y_round` (`CatchUp/Hyb2.lean`) | formalized | — |
| L26 | Token lemma | R finite, t = min R, any score s. If V(R − {t}, t) = draw (`valueAux (R.erase t) s (s + t) false = .draw`), then the level mover draws R: `valueAux R s s b = .draw` for either opening flag b | L6 | A7, A8 | `CatchUp.token_lemma` (`CatchUp/Token.lean`) | formalized | — |
| L27 | Two block families suffice | L12 at (a = 1, p even) and at (a = 2, p odd) implies L1: for N ≡ 0 mod 4, {1..N} is the block a = 1, p = N/2 at debt 0; for N ≡ 3 mod 4, {2..N} is the block a = 2, p = (N − 1)/2 (odd) at debt 1, and L26 with t = 1 gives value({1..N}) = draw | L26, L12 | all | `CatchUp.conjecture_of_two_families` (`CatchUp/Token.lean`) | formalized | — |
| L28 | Level law | At equal scores, if some pick t ∈ R leaves the opponent drawing (`valueAux (R.erase t) s (s + t) false = .draw`), the level mover draws: no pick wins. So a level position is a draw iff some pick draws. L26 is the case t = min R | L6 | A7, A8 | `CatchUp.level_law` (`CatchUp/Token.lean`) | formalized | — |
| L29 | One family at height 2 | If V({2..N}, 1) = draw (read at score 0) for every N ≥ 2 with 1 + … + N even, then L1. Both residues N ≡ 0, 3 mod 4 at once; necessary for N ≤ 35 (data: opening 1 draws there), open in general | L26 | A7, A8 | `CatchUp.conjecture_of_height_two` (`CatchUp/Token.lean`) | formalized | — |
| L30 | Two-token lemma | At equal scores: for picks y ≠ t, if the opponent cannot win after t (`valueAux (R.erase t) s (s + t) false ≠ .win`), it does not lose after y. Hence two distinct picks after each of which the opponent cannot win make the position a draw | L6 | A7, A8 | `CatchUp.level_option_ne_loss`, `CatchUp.two_token` (`CatchUp/Token.lean`) | formalized | — |
| L31 | One-sided roots | L1 follows from either (a) for every N ≥ 4 with even total, player 2 cannot win after the opening 1 nor after the opening 2; or (b) for every such N, the mover does not win {2..N} trailing by 1 (scores 0, 1) nor {3..N} trailing by 1 (scores 1, 2); N ≤ 3 directly | L30, L29 | A7, A8 | `CatchUp.conjecture_of_leader_pair`, `CatchUp.conjecture_of_suffix_pair`, `CatchUp.conjecture_le_three` (`CatchUp/Token.lean`) | formalized | — |
| L32 | TI at real heights | For p ≥ 1 and real h > 0, B(h, p) = {h, h+1, …, h+2p−1} with the mover trailing by p mod 2 is a draw: for every h > 0 if p is even; for every h ≥ 1/2 if p ≥ 3 is odd; for every h ≥ 1 if p = 1. By scaling: every arithmetic progression with 4m terms is a Catch-Up draw. Contains L12 (integer h), hence L1 | — | A7 | — | conjecture | — |
| L33 | Sign lemma | V(S, g) = sign(m(S, g)), m the margin game: Catch-Up turns, payoff the mover's final score minus the opponent's, no early-loss rule (a stuck mover takes everything); m defined on multisets | — | A10, A12 | — | paper proof | — |
| L34 | Far blocks are a margin tolerance | S finite, E_k = k 4-blocks {x..x+3}, each above twice the total below it plus 10: m(S ∪ E_k, g) = sign(m)·max(\|m\| − 2k, \|m\| mod 2) with m = m(S, g); with L33, for sum(S) + g even, V(S ∪ E_k, g) = draw iff \|m(S, g)\| ≤ 2k (MT) | L33 | A10 | — | conjecture | — |
| L35 | Sliding quadruple (Const) | For N ≡ 0, 3 (mod 4), N ≥ 4: V({1..N−4} ∪ ({N−3..N} + c), 0) is the same for every integer c ≥ 0 (exact for N ≤ 20). With L34 (FB: k = 1) and L1(N − 4) it gives L1(N); at c = 0 it is L1(N) itself | L34 | A10 | — | conjecture | — |
| L36 | Twins with a tie-break (TD's first cell) | For B the odd numbers {1, 3, …, 2p − 1} or the even numbers {2, 4, …, 2p}: the pairs {x, x + ε} (x ∈ B), ε > 0 smaller than 1/(p + 1), with the mover trailing by ε·(p mod 2), draw. The first cell of A11's homotopy | — | A11 | — | conjecture | — |
| L37 | Gap bound (LG) | (refuter-checked on ~80G positions) For every finite multiset S of positive integers and every d ≥ 0: m(S, d) ≥ −γ(S ⊎ {d}), γ(W) the largest gap between consecutive elements of sorted W ∪ {0}. Tie form G: \|m(S, 0)\| ≤ γ(S). G for all multisets ⇔ LG; G({1..N}) with an even total gives L1 (via L33) | L33, L38 | A12 | — | conjecture | — |
| L38 | Margin two-token lemma | At a tie on a multiset S, for openings of distinct values y < t: A(S, t) + A(S, y) ≥ 0, A(S, x) = m(S − x, x) the opponent's value after the opening x. Hence G at S follows from two distinct openings x with A(S, x) ≤ γ(S) | — | A12 | — | paper proof | — |

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

## L8 Pair sets draw
**Proof.** None: false (O7). True for p ≤ 2 (L7, L11) and far-apart pairs (L9).
**Evidence.** `pair_sets 30`: all 1,346,268 E and 317,811 T sets ⊆ {1..30} draw at g0; independent DP agrees on {1..26} (log 2026-10-22: sets made of adjacent pairs draw).
**Refuted** (O7; log 2026-10-22: pair sets do not all draw): V({17,18,20,21,25,26,28,29,31,32}, 1) = loss; {1,2} ∪ that set is a player-1 win. Refuter (claim mode): BROKEN; confirmed with `Solver`. No exception found with p ≤ 4.

## L9 Far-apart pairs
**Statement.** P_i = {a_i, a_i + 1}, 1 ≤ i ≤ p, σ_i = sum(P_1 ∪ … ∪ P_i), with (A) a_1 ≥ p and (F) a_{i+1} > σ_i + a_i + 1. For S = P_1 ∪ … ∪ P_p and 0 ≤ g ≤ a_1: V(S, g) = f_p(g), where f_j(d) = draw if d ≤ j and d ≡ j (mod 2), win if d < j and d ≢ j, loss if d > j. At g = p mod 2 this is L8 (E) for these sets.
**Proof.**
- *Terminal games.* For f: ℕ → outcomes, G(∅, g; f) = f(g); for L ≠ ∅, G(L, g; f) = max over x ∈ L of neg G(L − x, x − g; f) if x ≥ g (the turn ends), else G(L − x, g − x; f) (the mover continues). With f_0 (draw at 0, loss above) G = V: `valueAux` depends only on the deficit, a mid-turn deficit d acts like gap d, `best` is the max (L6), and for g > sum(L) both give loss (in G every pick keeps the mover behind until L runs out at deficit ≥ 1). Every deficit reached in G(L, g; f) is ≤ max(g, max L), since a turn ends with a lead at most its last pick (below it unless the turn started at deficit 0); so G reads f only there.
- *(P1) One pair.* For a ≥ d: G({a, a+1}, d; f) = max(f(d + 1), x), x = neg f(1) if d = 0, else f(d − 1). Taking a ends the turn; the opponent's only pick a + 1 ends theirs with lead d + 1. Taking a + 1 ends the turn; the opponent takes a and is then behind by 1 with nothing left if d = 0, else ahead by d − 1. With f = f_j this is f_{j+1}(d): for d ≥ 1, d ± 1 have the same parity and f_j(d + 1) ≤ f_j(d − 1), so the max is f_j(d − 1) = f_{j+1}(d); for d = 0 it is max(f_j(1), neg f_j(1)), win for j even (f_j(1) = win, or loss at j = 0), draw for j odd.
- *(P2) Top pair.* Let f(d) = loss for all d ≥ D, L a set with min L ≥ D + 1, h ≥ max L, P = {a, a + 1} with a > sum(L) + h. Then G(L' ∪ P, g; f) = G(L', g; f⁺) for all L' ⊆ L and g ≤ h, where f⁺(d) = G(P, d; f). Induction on |L'|; L' = ∅ is the definition of f⁺. For L' ≠ ∅, a pick from L' leads to gap x − g ≤ h or g − x < g, and the terms match by induction. Opening P loses: a + ε (ε ∈ {0, 1}) ends the turn (a > g); the opponent, behind by a + ε − g > sum(L'), takes all of L' while staying behind, then the partner a + 1 − ε, ending ahead by m = g + 1 − 2ε + sum(L') ≥ sum(L') − 1 ≥ D ≥ 0 with nothing left (m ≥ 0 is what makes the partner end that turn when ε = 1), and f(m) = loss for the opener. So the max runs over picks from L' only.
- *Peeling.* V(S, g) = G(S, g; f_0). For i = p down to 2 apply (P2) with L = P_1 ∪ … ∪ P_{i−1}, P = P_i, f = f_{p−i}, D = p − i + 1, h = a_{i−1} + 1 = max L: min L = a_1 ≥ p ≥ D + 1 by (A); a_i > σ_{i−1} + h by (F); g ≤ a_1 ≤ h. G(L, g; f⁺) reads f⁺ only at d ≤ h < a_i, where (P1) gives f⁺ = f_{p−i+1}. What remains is G(P_1, g; f_{p−1}) = f_p(g) by (P1), as g ≤ a_1.

In words: nobody opens a pair while a smaller number is left, because the opponent could then take everything below together with the partner. Pairs are opened from the bottom, each opened and closed in consecutive turns, and each pair turns the endgame f_j into f_{j+1}.
**Evidence.** `far_pairs` (log 2026-10-22: far-apart pairs proved): the smallest sequences satisfying (A), (F) with a_1 − p ∈ {0, 1, 5}, p ≤ 7 (largest number 28,198), match f_p at every g ≤ a_1. Every pair set with p = 2 (max ≤ 80) and p = 3 (max ≤ 60) in which each pair exceeds the sum below it matches f_p at g ≤ min(p + 1, a_1). (A) is needed: {1,2,4,5,13,14,40,41} (F0 without (A)) and {1,2,6,7,24,25,91,92} ((F) without (A)) are losses at g = 1 = a_1 where f_4(1) = win; every failure without (A) up to max 200 has a_1 = 1, and none is at g0 (refuter). (A) with F0 instead of (F) held on all sets with p ≤ 4 and max ≤ 200, but (P2) itself fails under F0 (24 of 1.43M cases, outside what peeling uses), so dropping (F) needs a different induction. Refuter (proof mode, 2026-10-22): SURVIVES; every step checked numerically with its own engine (G = V; the read bound, which is tight; (P1) for j ≤ 20; (P2) on 800 random instances with arbitrary L, 389,848 cases; peeling on random sequences, 4.6M identities; the full statement on 1,650 random sequences with p ≤ 7). Its first two notes are the wording fixes above.

## L10 Reductions within L8
**Statement.** (a) For T = {1,2,3} ∪ E', E' a pair set above 3 with p pairs: V(T, p mod 2) ≥ neg V({2,3} ∪ E', (p + 1) mod 2). {2,3} ∪ E' is a pair set with p + 1 pairs at its g0, so L8 (E) for it gives V(T, g0) ≥ draw. (b) For a pair set E with p pairs, p even: if V(E ∖ P, 1) = draw for every pair P = {a, a+1} of E, then V(E, 0) ≤ draw.
**Proof.** `valueAux`'s early loss (the mover cannot catch up with everything left) never fires at the nodes used: each player concerned has enough left (in (b), E ∖ P ≠ ∅ as p ≥ 2). V depends only on the deficit, not on the base scores (a helper fact for Lean, also used by L9). (a) Pick 1. If p is even the gap is 0 and the turn ends with the mover ahead by 1: the opponent trails by 1 with {2,3} ∪ E'. If p is odd the gap is 1 and 1 catches up exactly: the opponent moves at gap 0 with {2,3} ∪ E'. By L6 the value is at least this pick's value. (b) By L6 it suffices that every pick has value ≤ draw. A pick at gap 0 ends the turn. If the mover takes a + 1, the opponent, behind by a + 1, takes a and is still behind by 1 with E ∖ P: that continuation is worth V(E ∖ P, 1) = draw to the opponent, so the opponent's value is ≥ draw and the pick's ≤ draw. If the mover takes a, the opponent takes a + 1 and leads by 1: the mover faces V(E ∖ P, 1) = draw, so the opponent's value is ≥ draw again.
**Evidence.** `pair_moves 28` (log 2026-10-22: pair sets, first picks): in all 121,393 T sets ⊆ {1..28} pick 1 and pick 3 draw. Refuter (proof mode, 2026-10-22): SURVIVES; own DP and a literal port (agreeing with OEIS A278587): (a) on all T ⊆ {1..26} with equality for pick 1; (b) on all even-p E ⊆ {1..26}, and both partner inequalities on every R ⊆ {1..26} (419M checks). The analogue of (b) for p odd fails: after a bottom pick and the partner reply the mover trails by 2 with an even number of pairs, a mover win in 446 E sets ⊆ {1..28} (smallest {2,3,4,5} at gap 2: pick 4 wins), so the defender must sometimes refuse the partner (O6).

## L11 Two pairs
**Statement.** For 1 ≤ a and b ≥ a + 2: V({a, a+1, b, b+1}, 0) = draw.
**Proof.** ≤ draw: L10 (b), since V({a, a+1}, 1) and V({b, b+1}, 1) are draws by L7 (g = 1 ≤ x and g + x = y). ≥ draw: pick a + 1 (L6); the opponent trails by a + 1 with {a, b, b+1}, and by L7 for the two numbers left:
- a first: still behind by 1, then V({b, b+1}, 1) = draw for the opponent.
- b first: catches up, leads by g = b − a − 1 ≥ 1; the mover trails by g with {a, b+1}: if g ≤ a, g + a = b − 1 < b + 1; else g < a + b + 1. A mover win either way.
- b + 1 first: leads by g = b − a; the mover trails by g with {a, b}: if g ≤ a, g + a = b, a draw; else g < a + b, a win.
So the opponent's best is a draw, and the pick a + 1 is worth a draw.
**Evidence.** `pair_sets 30` (all 2-pair sets ⊆ {1..30} draw at gap 0); `far_pairs` part 2 (all 2-pair sets with max ≤ 80, gap 0). Refuter (proof mode, 2026-10-22): SURVIVES; literal port on all a + 2 ≤ b ≤ 61 with every sub-claim of the proof, edge cases b = a + 2 and a = 1 checked.

## L12 Even blocks draw
**Proof.** Open. p ≤ 2 for every a: L7 (p = 1), L11 (p = 2).
**Evidence.** `block_rows 8 80` (log 2026-10-22: even blocks draw at every height, but the band can shrink): every block with p ≤ 8, a ≤ 80; refuter's own engine: also a ≤ 200, and p = 9, 10 at a ≤ 80. From a ≥ a0(p) ≈ 2p the row at gaps below a is t_p (draw at draw-parity g ≤ p, win at 0 for p odd, loss otherwise). Unlike pair sets (O7), blocks show no exception at any height. The band is not monotone in a (O9).

## L13 High sets are the rounds game
**Rounds game.** For O with \|O\| even: R(O, d), the mover trailing by d ≥ 0. A round: the mover picks i ∈ O, then the other picks j ∈ O − {i}; the mover's signed debt becomes δ = d + j − i; if δ ≥ 0 the mover moves first in the next round at debt δ (a tie keeps the mover), else the other does, at debt −δ. O empty: draw at debt 0, else loss. Equivalently: one pick each per round, the player behind picks first (at a tie, the previous first picker), higher total wins.
**V.** V(S, g) = `valueAux S s (s+g) false` for any s: the mover's value trailing by g at a turn start. It depends only on the deficit, and a mid-turn node equals a turn start with the same scores (`valueAux` has no turn flag, only the opening flag). value(S) = V(S, 0), since at 0–0 every pick catches up, so the opening flag changes nothing.
**Proof.** Claim, by induction on \|O'\| (\|O'\| even): V({a + o : o ∈ O'}, d) = R(O', d) whenever d + sum(O') < a. For O' = ∅ both are draw at d = 0 and loss otherwise. Otherwise the mover trails by d < a, so any pick a + i ends its turn; the other then trails by a + i − d. Its pick a + j catches up iff j ≥ i − d; then the first mover trails by δ = d + j − i ≥ 0 at a turn start. If j < i − d, the other still trails by i − j − d = −δ, with 0 < −δ < a: if numbers remain, its next pick ends its turn, and that pick is the first of the next round with the other as mover at debt −δ; if none remain (O' − {i, j} = ∅), the empty-set rule, or the early-loss rule one step earlier, scores a loss for the other, as R does at positive debt. In both cases O'' = O' − {i, j} satisfies the hypothesis: d + j − i + sum(O'') = d + sum(O') − 2i < a for δ ≥ 0, and i − j − d + sum(O'') = sum(O') − d − 2j < a for δ < 0. Same player to move, same options, same terminal outcomes; best is the maximum by L6, so the values agree. The early-loss rule fires nowhere else: a mover at debt < a with a number left catches up with one pick, and the other, trailing by a + i − d < 2a, catches up with two whenever two remain; c = 1 nodes always have an odd count left because \|O'\| is even.
**Lean (2026-10-26).** `CatchUp.valueAux_map_add`: for `Even O.card` and `d + ∑ O < a`, `valueAux (O.map (addLeftEmbedding a)) s (s + d) false = roundsValue O d` for every s. Deviations: `roundsValue` is also defined for odd O (the mover wins when no answer is left; never used); s stays universally quantified in the induction instead of the paper's "V depends only on the deficit"; the early-loss rule is handled at the other player's node, where it fires only with one number j left and d + j < i, as in the proof above.
**Refuter.** Claim mode (2026-10-26): 866k comparisons with a literal `valueAux` port, 0 mismatches; a = g + sum(O) also matches, the first mismatches are at g + sum(O) − 2. Proof mode (2026-10-26): SURVIVES; its wording fixes are adopted here (V defined, \|O\| even, the tie in the "equivalently", the per-round form of the bound, the induction made explicit); its step checks covered 1.78M nodes.

## L14 Greedy bound
**Proof.** Induction on \|T\|; it suffices that each round satisfies (Z's pick − Y's pick) ≥ c_td(T') − c_td(T), T' = T minus the two picks. Sort t1 > t2 > …; c_td is the alternating sum t1 − t2 + t3 − …. If Y takes t1 (picking first), Z takes t2: both sides equal t2 − t1. Otherwise Z takes t1 and Y takes some t_j, j ≥ 2, in either order (this includes Y picking first a non-maximal number). Removing t1 and t_j flips the signs of t2..t_{j−1} and keeps those after t_j; with A = −t2 + t3 − … ± t_{j−1}: c_td(T) = t1 + A ± t_j + tail and c_td(T') = −A + tail. The required inequality t1 − t_j ≥ −2A − t1 ∓ t_j becomes 2[(t1 − t2) + (t3 − t4) + … + (t_{j−2} − t_{j−1})] ≥ 0 for j odd and 2[(t1 − t2) + (t3 − t4) + … + (t_{j−1} − t_j)] ≥ 0 for j even. Both hold.
**Lean (2026-10-26).** `altSum T` = max T − altSum (T minus its max), the alternating sum by recursion. `greedyWorst T`: the worst case over Y's picks and the order, each round either Z takes t1 and Y some j (either order; same totals) or Y takes t1 first and Z the next largest; odd T gets a convention (Z takes the last number), unused. `neg_altSum_le_greedyWorst`: −altSum T ≤ greedyWorst T for even T. Deviation: the per-round inequality is proved through one joint lemma, x ≤ altSum U + altSum (U − x) ≤ 2·max U − x for x ∈ U (induction removing the maximum), instead of the sign bookkeeping above; it gives both directions, \|c(T) − c(T')\| ≤ t1 − t_j (`altSum_round`), so L18's part (a) is formalized as well.
**Evidence.** `scratch/b20/greedy.py 10`: Y's best, also choosing the order, gives exactly −c_td(T) on every even T ⊆ {0..9} (tight). Refuter proof mode (2026-10-26): SURVIVES; per-round inequality on all even T ⊆ {0..11} in both orders and on 6,000 random sets and multisets; statement made precise as above. L15's proof does not use it.

## L15 Always-max on pair sets
**Terms.** Z plays always-max, Y anything; s = Z's margin (Z's initial lead plus Z's picks minus Y's picks). A remainder is a number left whose partner is taken; it is owed to the player who did not take the partner. Φ = s + (remainders owed to Z) − (remainders owed to Y). u = pairs taken wholly by Z − pairs taken wholly by Y (doubles). A round start is balanced if u = 0. At the end there are no remainders and u = 0 (both players take p numbers), so the end is a balanced start and the final margin is Φ there.
**Proof (the balanced-start potential and the stretch count are the ideator's, 2026-10-26).** Joint induction over balanced starts in time order: Φ ≥ −1, and at a balanced start with remainders Y moves with s ≥ 1.
- *Fact A.* Every number Z holds exceeds every number left (Z always took the maximum). So a remainder owed to Y arises only when Z takes the high x+1 of an intact top pair; x is then the maximum, and Z's next pick takes it unless Y does first. Hence at most one remainder owed to Y exists, and it is the maximum.
- *Fact B.* At a round start both have taken equally many numbers, so #(owed to Z) = #(owed to Y) + 2u. Hence u ≥ 0, and a balanced start is either orphan-free or has exactly x (owed to Y, the maximum) and one w < x (owed to Z).
- *Fact C.* Effect on Φ of each pick. Z (its maximum is a fresh high, a remainder owed to Z, or x; never a fresh low): opens +1, closes 0, doubles +2x. Y: opens with a high −1, opens with a low +1, closes x 0, doubles a remainder w owed to Z −2w.
- *Base.* Every start of the statement is orphan-free with Φ = s ≥ −1. Orphan-free balanced starts have Φ = s, so by the mover rule Z moves there only at s ∈ {−1, 0} and Y moves there only at s ≥ 0.
- *x-and-w starts.* Such a start is reached in one of three ways. (i) From an orphan-free start (s ≥ −1, and s ≥ 0 if Y moves), Z takes x+1 and Y takes some y ≤ x − 1 from a lower pair, in either order: s' = s + x + 1 − y ≥ s + 2 ≥ 1. (ii) From an x-and-w start, Y closes x and Z opens the next top x′+1: then Φ' = Φ + 1 ≥ 0, and x′ > w because Z's maximum x′+1 exceeds w; so s' = Φ' + x′ − w ≥ 1. (iii) A stretch ends there with Φ ≥ 0 (below), so s = Φ + x − w ≥ 1. In each case s ≥ 1, so Y moves.
- *(P1) One round to the next balanced start.* Orphan-free, Z moves: Z opens the top (+1); Y closes (0) or opens elsewhere with a high (−1) or a low (+1): ΔΦ ≥ 0; Y cannot double. Orphan-free, Y moves: Y takes the top of the top pair and Z its partner (the basic round, −1, from Φ = s ≥ 0); Y takes the bottom of the top pair and Z the top (+1); Y opens a lower pair (±1) and Z opens the top (+1): ΔΦ ≥ 0. With x and w, Y moves: Y closes x and Z opens the next top (+1) or closes w (0); Y doubles w (−2w) and Z doubles x (+2x): ΔΦ = 2(x − w) > 0. The remaining option, Y opening a fresh pair, makes Z double x and starts a stretch.
- *(P2) Stretch.* A stretch is the run of rounds from a balanced start to the next one, with u ≥ 1 at the inner starts. Its first round is Y opening a fresh pair (u stays 0) and Z doubling x (u = 1); since one pick changes u by at most 1 and u ≥ 1 at inner starts, u ≥ 0 at every moment of the stretch. Each player picks once per round and makes c ≥ 1 doubles in the stretch (it ends at u = 0), so counting picks turns Fact C into ΔΦ = 2·(Y's low openings) + (Y's closes) − (Z's closes) + 2Σ_j (x_j − w_j), pairing Z's j-th double x_j with Y's j-th double w_j in time order. Since u ≥ 0 throughout, Z's j-th double comes before Y's j-th; w_j was still left when x_j was the maximum, so x_j > w_j. A close by Z at u ≥ 1 takes the current maximum h; assign it to j = (Y's doubles so far) + 1 ≤ (Z's doubles so far). Y's j-th double exists because the stretch ends at u = 0, and comes later, so x_j > h > w_j. Distinct closes take distinct numbers, so at most x_j − w_j − 1 closes are assigned to j. A Z close at u = 0 happens only in the exit round, after Y's last double (when Y doubles to u = 0 and Z doubles back, Z's pick is a double, not a close); the exit round can also hold a close at u = 1 before Y's last double, assigned to j = c. So Z's closes ≤ Σ_j (x_j − w_j − 1) + 1, and ΔΦ ≥ Σ_j (x_j − w_j) + c − 1 ≥ 2c − 1 ≥ 1.
- Hence Φ ≥ −1 at every balanced start, in particular at the end. ∎
**Evidence.** `max_strategy 22 8`: every pair set within {0..21} (p ≤ 11), leads ≤ 8; least margin 0 or −1 by parity, l − p for a lead l > p. Refuter claim mode (2026-10-26): SURVIVES on all 75,025 pair sets within {0..25} (p ≤ 13), leads ≤ 14, and random sets with spacing up to 200; one gap 2 breaks it ({0,2,4,5} at debt 1), so the unit gaps are essential. Refuter proof mode (2026-10-26): SURVIVES. From every balanced state meeting the induction hypotheses (not only reachable ones) it followed every Y line to the next balanced start: every path within {0..13} (270M paths), memoized within {0..17} (3.3M starts). Facts A–C, the ten (P1) classes, the counting identity, the order and assignment of doubles and closes, and ΔΦ ≥ Σ(x_j − w_j) + c − 1 all hold, the last tightly; at every x-and-w start reached Y moves with s ≥ 1. A mutation test (allowing Φ = −2, or Z moving at x-and-w starts) produces violations. Round-by-round potentials fail (an earlier route via L14, and a reserve-based potential, closed only to p = 5: log 2026-10-26).

## L16 High pair sets draw
**Proof.** From L13 and L15. The rounds game takes all 2p numbers (no early loss), so the final margin is the initial lead plus a difference of the two players' totals from E, and sum(E) ≡ p gives margin ≡ g0 + p ≡ 0 (mod 2) for both players. So a margin ≥ −1 is ≥ 0, and always-max secures it for the mover (start at debt g0 ≤ 1) and for the other player (leading by g0 ≥ 0). Both secure at least a draw, so R(E, g0) = draw; L13 transfers it to V for a > g0 + sum(E), which a > 1 + sum(E) ensures.
**Evidence.** Refuter (claim mode, 2026-10-26, C3): every pair set with p = 2..9 and spacing up to max offset 200 (p ≤ 4), 80 (p = 5), …, 30 (p = 9), and every pair set within {0..25}, matches t_p at debts 0 and 1. Our `rounds_game 24`: all pair sets within {0..23}. Refuter proof mode (2026-10-26): SURVIVES; always-max from every start of L15 on the 4,181 pair sets containing 0 within {0..19} (least margin −1); a literal `valueAux` port gives draws on all 232 pair sets within {0..11} at a = sum(E) + 2 and a = sum(E) + 1 + g0.
**Lean, blocks** (2026-10-26, `CatchUp/Blocks.lean`). `block_draw_high`: for p ≥ 1 and a > p mod 2 + p(2p−1), `valueAux ((range (2p)).map (a + ·)) s (s + p % 2) false = draw` for every s, i.e. V({a..a+2p−1}, p mod 2) = draw. Deviations from L16: blocks only, not every pair set; the margin bound comes from L23 (`depth_class_roundsMargin`, AM+T) instead of L15 (always-max); the height is L13's a > g + sum, the same as L16's for p odd and one lower for p even. Parity via `even_roundsMargin_add`, the value via `roundsValue_eq_ofMargin`, the real game via `valueAux_map_add`. L16 itself stays `paper proof` (general pair sets). `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.

## L17 Rows of high blocks
**Proof.** Partial: the draw entries (d ≤ p, d ≡ p) by L23 with parity; the losses for d > p by L20. Open: the parity-forced entries (loss at d ≤ p with d ≢ p, win at d = 0 for p odd), B33.
**Lean, blocks** (2026-10-26). `block_row_draw_linear`: for p ≥ 1, a > 3(2p−1), d ≤ p with d ≡ p (mod 2), V({a..a+2p−1}, d) = draw (every s), by L21's Hyb on AM+T; at Z's start as the other player the debt d falls in either branch of `HY` (d ≤ c(R) before the switch, else after it with d + c(R) ≤ 3(2p−1)). Deviations: the real game at linear height instead of the rounds game, the draw entries only. `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.
**Evidence.** `rounds_game 24` (p ≤ 12); refuter (C2): p ≤ 13 at every debt, p = 14 at d ≤ 14.

## L18 Catch-up potential step
**Proof.** Write c' = c_td(T') for the set T' left after the round; c_td(∅) = 0, so Γ = s at ∅ agrees with both formulas. (a) Z moves (s ≤ 0) and takes t1; Y takes t_j. Removing t1 and t_j flips the signs of t2..t_{j−1} in the alternating sum, so c − c' = t1 + 2A ± t_j with A = −t2 + t3 − … ± t_{j−1}, and t1 − t_j ≥ c − c' reduces to (t2 − t3) + (t4 − t5) + … ≥ 0 (up to t_{j−1} for j even, up to t_j for j odd; equality at j = 2). So s' + c' ≥ s + c. This shares L14's sign bookkeeping but is the other direction: L14 says s − c never decreases. If Z moves next (s' ≤ 0, including a tie, which keeps Z's move), Γ' = min(s' + c', 0) ≥ Γ; if Y moves next, Γ' ≥ 0 ≥ Γ. (b) Y moves (s ≥ 0). If Y takes t_i with i ≥ 2, Z's largest is t1 > t_i, so s' = s + t1 − t_i > 0: no exception, Y moves next, and L14's per-round inequality (Z took the largest) gives s' − c' ≥ s − c, so Γ' ≥ Γ. If Y takes t1 and Z answers t2: s' = s − (t1 − t2) and c' = c'' = c − (t1 − t2). If s' > 0, Γ' = max(s' − c'', 0) = Γ; s' = 0 happens only at \|T\| = 2 (for \|T\| ≥ 4 the exception applies), where the game ends at 0 = Γ. If s' < 0, Γ = 0 (s < t1 − t2 ≤ c) and Γ' = min(s − (t1 − t2) + c'', 0), which is ≥ 0 iff s ≥ (t1 − t2) − c''. If s = t1 − t2 and \|T\| ≥ 4, AM+T answers t3 instead: s' = t3 − t2 < 0 and c' = c_td({t2, t4, t5, …}) ≥ t2 − t4 > t2 − t3, so Γ' = 0 = Γ. Converse: for \|T\| ≥ 4, c'' > 0, so s < (t1 − t2) − c'' excludes s = t1 − t2; AM+T answers t2 and Γ drops by (t1 − t2) − c'' − s. At \|T\| = 2 the game ends: Y takes t1, Z takes t2, final s − (t1 − t2). ∎
**Evidence.** `scratch/b20/gammastep_check.py 13 16`: on every even T ⊆ {0..12}, \|s\| ≤ 16, both movers (139,230 states), the drop occurs exactly when the statement says. Along play from {0..2p−1} under AM+T with d ≤ p, Γ drops at most once, by 1, in a last round (`gammastep.py 10`); with d = p + 1 a drop of 1 can also come at \|T\| = 4 (refuter: {5,2,1,0}, Y moving at s = 1), still at most 1 per line over all starts with p ≤ 9. Refuter proof mode (2026-10-26): SURVIVES; independent check with a literal rounds-game move generator on every even T ⊆ {0..13}, debts ≤ 40, both movers (671,662 states) and 6.26M random states near the thresholds, 0 mismatches; moving the threshold by ±1 gives mismatches. Plain always-max satisfies the same statement (the exception state then gives a tie with Γ' = 0 = Γ), so the tie rule matters only for L19 and the parity-forced wins. Use: if every state where Y moves satisfies s ≥ (t1 − t2) − c'' (and at the last round s ≥ t1 − t2 − 1), Z ends with margin ≥ Γ0 − 1.
**Lean** (2026-10-26, `CatchUp/Potential.lean`). `potential_le_roundsMargin`: for any class of states closed under AM+T's rounds in which every Y-moving state meets the condition (e ≥ (t1 − t2) − c'' at \|T\| ≥ 4, e ≥ t1 − t2 − 1 at \|T\| = 2), Z's minimax margin is at least Γ − 1. Deviations: the per-round step is proved inside this induction rather than as a separate lemma, and only in the direction used; the converse (the drop happens exactly under the condition, by that amount) is not formalized. The signed lead s is two debts: d when Z moves (s = −d), e when Y moves (s = e), with Z's margin −`roundsMargin T e`. AM+T's answer is `amtReply` (exact tie: e + max left = Y's pick, with another number left). In the exception round Lean uses c' ≥ t2 − t3 (from `altSum_le_max'`) instead of c' ≥ t2 − t4 > t2 − t3. `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.

## L19 Top-run lemma
**Proof.** Open. Wanted: an invariant along play that gives the condition where Y moves. Along play from {0..2p−1}: at every Y-moving start, s + \|T\|/2 ≥ H + 2 (\|T\| ≥ 4) and ≥ H + 1 (\|T\| = 2), H = numbers missing between min T and max T; this implies the condition, since c_td(T − {t1, t2}) ≥ \|T\|/2 − 1. No invariant of the form s + \|T\|/2 − a·(holes inside top-down pairs) − b·(holes between them) ≥ k is closed over all sets (`scratch/b20/invsearch.py 9 10`): the positions of Y's holes matter. Reachable Z-moving sets from intervals are intervals with at most two short hole runs (`zshapes.py 7`).
**Evidence.** `scratch/b20/toprun2.py 17`: all 987 pair sets containing 0 within {0..16}, every start with d ≤ r and every lead l ≤ p + 1: the condition holds at every reachable Y-moving state. `toprun.py 14`: for d = r + 1 it fails on many sets, and Z's guarantee drops below −1 on some. `ycond.py 7`, `holes.py 8`: intervals, p ≤ 8.

## L20 Matching bound
**Proof.** Call π(i) the partner of i in the bottom-up matching of the numbers left R. The mover, at debt d > c(R), picks i; the other answers π(i); the new signed debt is δ = d + π(i) − i ≥ d − \|π(i) − i\|. Removing a matched pair keeps the other pairs consecutive in sorted order, so c(R − {i, π(i)}) = c(R) − \|π(i) − i\| and δ − c(R'') ≥ d − c(R) > 0. Hence δ > 0: the mover moves again, at a debt above c of what is left. At R = ∅ the debt is still ≥ d − c(O) > 0, a loss. ∎
**Evidence.** Stated as U0 in `scratch/b20/NOTES.md`; `rounds_game` treats debts ≥ U as losses by it and matches an uncut search (log 2026-10-26). Refuter proof mode (2026-10-26): SURVIVES; every even O ⊆ {0..9}, d ≤ c + 3 (1,533 cases): R = loss, and the partner strategy's worst final margin is exactly d − c(O) (tight).
**Lean** (2026-10-26, `CatchUp/Matching.lean`). `matchCost` pairs the two smallest numbers and recurses. `roundsMargin_le_matchCost`: for even O and matchCost O < d, `roundsMargin O d ≤ matchCost O − d` (the mover's minimax margin; with `roundsValue_eq_ofMargin` the value is a loss). Deviation: the other player's answer is any j with c(O − {i, j}) + \|i − j\| ≤ c(O) (`exists_partner`, proved by induction removing the two smallest, which yields the matching partner) instead of the partner named explicitly. `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.

## L21 High pair sets at linear height
**Strategy (Hyb, the ideator's, 2026-10-26).** Z takes the largest number left, as first picker and as answerer, until the first round start where Y moves at a debt e > c(R) (R the numbers left, c as in L20); from then on Z answers each Y pick with its L20 partner. In the real game, rounds are numbered as in L22.
**Proof.** Work in the rounds game R(E, g) with g = p mod 2 ≤ 1; p ≥ 1 gives m ≥ 1 ≥ g. Every R ⊆ E has c(R) ≤ max R − min R ≤ m (the matched gaps are disjoint intervals).
- *(a) Debts.* Along every play consistent with Hyb, every round start has debt ≤ 3m. Before the switch Z picks the largest. Z moving at debt d: Z takes t1, Y some t_j; δ = d + t_j − t1 ≤ d, so Z moves next at ≤ d, or Y at t1 − t_j − d ≤ m. Y moving at e ≤ c(R) ≤ m (no switch): Y takes i, Z the largest j left; Y moves next at e + j − i ≤ 2m, or Z at i − j − e ≤ m (only if i > j, so i = t1, j = t2). So before the switch Z's debts are ≤ max(g, m) and Y's ≤ max(g, 2m). After the switch only Y moves (L20), and each round raises its debt by at most the removed pair's gap; these gaps sum to c(R) ≤ m at the switch. So every debt is ≤ max(g, 2m) + m = 3m.
- *(b) Same game.* By (a) and a > 3m ≥ max E, L22 applies to σ = Hyb: every real-game play against Hyb is a rounds-game play against Hyb with the same outcome.
- *(c) Guarantee.* A play that never switches is a whole always-max play from an L15 start (Z moving at debt g ≤ 1, or Z as the other leading by g ≥ 0), so L15 gives Z's final margin ≥ −1; L15 holds for every play, so it applies play by play. A play that switches is a loss for Y by L20 alone.
- *(d) Parity.* The rounds game takes all numbers, so the final margin is g plus a difference of the two players' totals, ≡ g + sum(E) ≡ g + p ≡ 0 (mod 2), and ≥ −1 means ≥ 0. Both players secure at least a draw this way, so R(E, g) under Hyb gives Z ≥ draw in both roles, and by (b) so does V: the value is a draw. ∎
**Evidence.** Ideator (scratch, `scratch/ideator/a7/`): Hyb keeps always-max's margins (p ≤ 10); in the real game Hyb draws blocks at g0 in both roles for every a ≥ 4p − 6 (p = 3..8), and all 1,597 pair sets containing 0 within {0..17} at a = 3·span + 1..3. Refuter proof mode (2026-10-26): SURVIVES. (a)'s bounds hold on all 4,181 pair sets containing 0 within {0..19} and on all even sets containing 0 within {0..14}, both roles; the largest round-start debt reached is 2m − 3 (4p − 5 for blocks), at most 1.842m. Its own literal `valueAux` port (reproduces OEIS A278587 for n = 3..16 and O7's loss): on all 610 pair sets containing 0 within {0..15} at a = 3m + 1, 3m, 3m − 1, 3m − 2, both roles, Hyb never loses and V = draw; per-node comparison of rounds-game and real-game outcomes against Hyb at a = max(D, m) + 1 (D the largest debt reached), 650,774 nodes, 0 mismatches. Hyb's largest losing height within {0..13} is 1.615m; on O7's set it loses at a = 24 and holds from a = 26. Mutation (switch two steps early): 397 negative margins.
**Lean, blocks** (2026-10-26, `CatchUp/Linear.lean`). `block_draw_linear`: for p ≥ 1 and a > 3(2p−1), `valueAux ((range (2p)).map (a + ·)) s (s + p % 2) false = draw` for every s, i.e. V({a..a+2p−1}, p mod 2) = draw, the same range as above (a ≥ 6p − 2). Deviations: blocks only, not every pair set; before the switch Z plays AM+T (L23) instead of always-max, so (c) uses L23's classes (`KZc`, `KYc`) and not L15; (a) is the invariant "Z's debt ≤ m; before the switch Y's debt ≤ c(R) and ≤ 2m; after it c(R) < Y's debt and debt + c(R) ≤ 3m" (`HZ`, `HY`), with c(R) ≤ max R − min R as `matchCost_le_span`; parity (debt + sum of the numbers left even) is carried in the classes instead of (d)'s final count; (b) is `valueAux_transfer` (L22). `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.

## L22 Strategy transfer
**Proof.** L13's proof, read one round at a time; it uses only that the round's start debt d is below a and that max O < a. The mover's pick a + i ends its turn (a + i > d), so it is round k's first pick. The other trails by a + i − d < 2a; its pick a + j catches up iff j ≥ i − d (an exact tie, δ = 0, passes the turn back to the round's mover, as R's tie rule says), and that is round k's second pick. Otherwise it still trails by i − j − d ≤ max O < a; `valueAux` has no turn flag, so this node is a turn start, and its next pick is round k + 1's first, with the other as mover at debt −δ = i − j − d. The early-loss rule fires only at a round's answerer with one number left and j < i − d, which R scores as a loss too; with nothing left the trailing player loses in both. So, while the round starts reached have debt < a, the real game and R have the same options, the same next round start and the same terminal outcomes, and σ (applied to picks 2k − 1, 2k) is defined at every real-game node of these plays. Outcomes agree play by play; final margins agree except at early-loss endings, where the outcome is still the same loss. ∎
**Evidence.** Part (b) of L21's proof as first written; refuter proof mode (2026-10-26, with L21): checked by hand and per node (650,774 nodes, see L21).
**Lean** (2026-10-26, `CatchUp/Transfer.lean`). `valueAux_transfer`: the strategy is two classes of round starts, KZ (Z moves at debt d) and KY (the opponent moves at debt e), closed under its rounds (Z has a pick, resp. an answer to every pick, leading back into the classes); if every state has offsets < a and debt ≤ a + o for every offset o left, and KZ ∅ d forces d = 0, then from KZ states `valueAux` on the translated offsets is not a loss, from KY states not a win. Deviations: classes instead of a strategy function; only the draw threshold (Z does not lose), not "the same outcome play by play"; the debt hypothesis is weaker than the paper's (d ≤ a + min R instead of d < a, what L24 needs), and offsets < a is required per state. `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.
**Lean, relaxed** (2026-10-26). `valueAux_transfer` now needs offsets ≤ a (was < a), with d ≤ a + o unchanged: `o < a` was only used to keep the answerer clear of the early-loss rule (2a ≥ a + i), where o ≤ a suffices. Callers unchanged. `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.

## L23 Depth invariant
**Idea (the ideator's, 2026-10-26).** Charge each hole by its depth below the top; the class K is closed under every AM+T round. It replaces L18 + L19 for intervals.
**Proof.** Write a1 = t1 − t2, b1 = t2 − t3, G1 = a1 − 1, G2 = b1 − 1 (holes between t2 and t1, between t3 and t2), m = holes below t3, T'' = T − {t1, t2}, primes for the state after the round, q' = q − 1.
- *(A)* D_Z(T) ≤ D_Y(T): each hole below t2 counts t2 − h ≤ t1 − h; holes above t2 add more.
- *(B)* For q ≥ 2 and x ∈ T − {t1}: D_Y(T − {t1, x}) ≤ D_Z(T) + (t2 − x). x = t2: the holes of T − {t1, t2} are those of T below t3, each counting t3 − h ≤ t2 − h. t3 ≤ x ≤ t_{2q−1} (only x = t3 when q = 2): the new top is t2, the holes are those of T below t2 plus x, so equality. x = t_{2q}: the holes of T − {t1, x} are the holes of T between t_{2q−1} and t2, a subset of those counted by D_Z(T), and t2 − x ≥ 0.
- *(C)* D_Y(T) = G1(G1+1)/2 + (G2·a1 + G2(G2+1)/2) + (m(a1 + b1) + D_Y(T'')), grouping holes above t2, between t3 and t2, and below t3 (depth from t1 = a1 + b1 + depth from t3). For q ≥ 2 (so t4 exists): D_Y(T'') − D_Z(T'') = G3(G3+1)/2 + m4(G3 + 1) with G3 = t3 − t4 − 1, m4 = holes below t4; this is ≥ 1 when m ≥ 1.
- *(D)* For T' = {a > b}, g = a − b: D_Y(T') = g(g−1)/2, D_Z(T') = 0. If s' ≥ 1 and s' + 1 ≥ g(g−1)/2, then s' ≥ g − 1 (for g ≥ 3, g(g−1)/2 − 1 ≥ g − 1; for g ≤ 2, s' ≥ 1 ≥ g − 1).
- *Last round* (T = {a > b}). Z moves: Z takes a, final s + a − b ≥ −1. Y moves (s ≥ a − b − 1): Y takes a, Z gets b (no exception: nothing else left), final s − (a − b) ≥ −1; Y takes b, final s + a − b ≥ −1.
- *(Z) Z moves, q ≥ 2.* Z takes t1, Y takes x. s' + q' = (s + q) + (t1 − t2 − 1) + (t2 − x) ≥ D_Z(T) + (t2 − x) ≥ D_Y(T') ≥ D_Z(T') by (B), (A). If Y moves next, s' > 0, so s' ≥ 1. At q' = 1: Y moving gives s' ≥ g − 1 by (D); Z moving gives s' + 1 ≥ D_Z(T') = 0, so s' ≥ −1 ≥ −(g + 1).
- *(Y1) Y moves, takes x ≠ t1.* AM+T takes t1 (a tie would need s + t1 − x = 0, impossible), s' = s + t1 − x ≥ 1, Y moves next. s' + q' = (s + q) + (t1 − x − 1) ≥ D_Y(T) + (t1 − x − 1) ≥ D_Z(T) + (t2 − x) ≥ D_Y(T'); the middle step needs D_Y(T) − D_Z(T) ≥ 1 − a1, true as the left side is ≥ 0 by (A). At q' = 1, (D).
- *(Y2) Y takes t1, s ≠ a1.* AM+T answers t2 (a tie needs s = a1); s' = s − a1 ≠ 0, T' = T''. By (C) and KY, s' + q' ≥ D_Y(T'') + [G1(G1+1)/2 + G2·a1 + G2(G2+1)/2 + m(a1 + b1) − a1 − 1].
  - Y moves next (s' ≥ 1), q' ≥ 2: if m ≥ 1 the bracket is ≥ b1 − 1 ≥ 0; if m = 0, D_Y(T'') = 0 and s' + q' ≥ 0 holds trivially. q' = 1 (holes below t3 are the m = G3 between t4 and t3, D_Y(T'') = m(m+1)/2): s' ≥ m(m+1)/2 + m·b1 + (m − 1)a1 − 2, which is ≥ m for m ≥ 2, and s' ≥ 1 ≥ m otherwise.
  - Z moves next (s' ≤ −1), q' ≥ 2: with D_Y(T'') ≥ D_Z(T''), the bracket is ≥ 0 when m ≥ 1, G2 ≥ 1 or G1 ≥ 3. Otherwise T − {t1} is an interval and G1 ≤ 2: G1 = 0 means no holes, s < a1 = 1 gives s = 0, s' = −1, and s' + q' ≥ 1 ≥ 0 = D_Z(T''); G1 = 1: KY gives s ≥ 1, s < 2, s' = −1; G1 = 2: s ∈ {1, 2}, s' ≥ −2 and q' ≥ 2; in both, s' + q' ≥ 0 = D_Z(T''). q' = 1: need a1 − s ≤ G3 + 2 = m + 2; if G1 ≤ m + 1, a1 − s ≤ G1 + 1 ≤ m + 2; else G1 ≥ 2 and KY gives s ≥ G1(G1+1)/2 − 2 ≥ G1 − 1, so a1 − s ≤ 2.
- *(Y3) Y takes t1, s = a1.* The exception: AM+T answers t3; s' = −b1, Z moves, T' = T − {t1, t3}, and D_Z(T') = D_Z(T'') (both count the holes below t4 by depth from t4). q' = 1: need b1 ≤ t2 − t4 + 1, true as t4 < t3. q' ≥ 2: by KY, q ≥ D_Y(T) − a1, so s' + q' − D_Z(T') ≥ G1(G1+1)/2 + G2·a1 + G2(G2+1)/2 + m(a1 + b1) − a1 − b1 − 1 + [D_Y(T'') − D_Z(T'')]. m ≥ 1: ≥ (m − 1)(a1 + b1) + ([D_Y(T'') − D_Z(T'')] − 1) ≥ 0 by (C). m = 0: need q ≥ G2 + 2; q' ≥ 2 gives q ≥ 3, enough for G2 ≤ 1; for G2 ≥ 2, q ≥ D_Y(T) − a1 ≥ (G2 − 1)a1 + G2(G2+1)/2 ≥ G2 + 2.
- *Intervals.* {0..2p−1} has no holes, so D_Y = D_Z = 0: Z moving at s = −d with d ≤ p satisfies s + p ≥ 0 (at p = 1, s ≥ −1 ≥ −2), and Y moving at s = l ≥ 0 satisfies KY. ∎
**Consequence.** With parity (the rounds game takes all numbers, so the final margin ≡ s0 + p(2p−1) ≡ d + p) the two players' AM+T guarantees give R({0..2p−1}, d) = draw for every d ≤ p with d ≡ p (mod 2): only the draw entries of t_p (L17). L20 gives the losses for d > p; the losses at d ≢ p, d ≤ p and the win at d = 0 for p odd need a guarantee of +1 and stay open (B33).
**Evidence.** Ideator (scratch, `scratch/ideator/l19/`): closure on all even T ⊆ {0..13} containing 0, \|s\| ≤ 95 (272,103 K-states), and independent code on all even subsets of {0..11} (113,972 K-states, Z's AM+T guarantee ≥ −1 at each); 184k random states near K's boundary (span ≤ 60, \|T\| ≤ 24); lemmas (A)–(C) on all 4,017 even T ⊆ {0..12} with \|T\| ≥ 4; each weakening (Z or Y threshold −1, dropping s ≥ 1, either last-round bound ±1, D_Y for D_Z) breaks closure. Under plain always-max closure fails only at Y-moving ties (refuter: 55 rounds over all even T ⊆ {0..11}), which is why always-max fails at d = p (−2 for p = 3..8). I checked (A)–(D) and every case above by hand (2026-10-26). Refuter proof mode (2026-10-26): SURVIVES, cases exhaustive (s = 0 for both movers included). Own code: closure on all even T ⊆ {0..15}, both movers, s from −40 to max(40, D_Y + 25) (1,000,627 K-states) and within {0..16}, \|s\| ≤ 100 (3,856,947), shifted sets included; Z's AM+T guarantee ≥ −1 against a perfect Y from all 987,901 K-states within {0..15}; every intermediate claim of every case checked literally (`cases.py 14 40`); (A)–(D) on 32,647 sets; 1,016,606 random boundary states; mutations (each threshold ±1, dropping s ≥ 1, D_Y for D_Z, plain always-max, a tie passing the move) all break closure. Exact minimax: R({0..2p−1}, d) = t_p for p ≤ 8, d ≤ p + 3.
**Lean** (2026-10-26, `CatchUp/Depth.lean`). `holes`, `depth` (D_Y) and `depthZ` (D_Z = depth of T without its top); classes `KZc T d` (Z moves trailing by d: s = −d) and `KYc T e` (the opponent moves trailing by e: s = e) with the last rounds as above, and at T = ∅ only Z's d ≤ 1; `closeZ`, `closeY` (cases (Z), (Y1)–(Y3)); `depth_class_roundsMargin`: Z's minimax margin ≥ −1 from `KZc`, the opponent's ≤ 1 from `KYc`; `kzc_range`, `kyc_range` for intervals. Deviations: (B)'s three cases are separate lemmas (`depth_erase_max'`, `depth_erase_inner`, `depth_erase_min'`); (C) is used as the one-step decomposition `depth_eq_erase_max'` applied twice with `card_holes_eq`, and the gap sums G(G+1)/2 are only bounded below (`gapSum_ge`: 2G ≤ gap sum + 1), which every case needs; the conclusion is the minimax margin bound rather than "every round ends in K". `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.

## L24 Blocks at the doubling-free height
**Proof (given (a)).** (b) *Transfer.* Let KZ, KY be the round starts (Z, resp. Y, to move) reached by plays consistent with Hyb2 from either start; they are closed under Hyb2's rounds by definition, since Hyb2 depends only on the current state. L22 in its formalized form (`valueAux_transfer`) needs at each of them only offsets ≤ a and debt d ≤ a + o for every offset o left (any single pick of the mover catches up), plus `hendZ`: a play ending at a Z start ends at debt 0, which is (c) + (d). With (a) and a ≥ 2p − 1 the bounds hold at every round start against Hyb2. (c) *Guarantee.* Before Hyb2 first finds a valid answer, Z plays AM+T (as first picker the largest), so play stays in L23's depth class (KZ, KY of L23): Z's margin ≥ −1. At the first switch Y's new debt is ≥ c(R''), Y keeps the move, and from a Y round start with debt e ≥ c(R) the L20 partner is a valid answer (L20's partner step c(R − {i, π(i)}) = c(R) − |π(i) − i|, `exists_partner` in Lean, not L20's strict statement), so Hyb2 always answers validly and Y's debt stays ≥ c of what is left; at the end Y's margin is ≤ 0. (d) Parity as in L21. (a) is L25: Y's round-start debts ≤ 2p − 1 + min R, Z's ≤ 2p − 1 ≤ a, which is all (b) needs.
**Evidence.** `hyb2_states 9 hyb2 reach`: (a) holds for p ≤ 9 with equality for p ≥ 3 (the bound is reached with {0, 1} left, Y trailing by 2p − 1, after Y takes i and Z i + 1 in each round after the switch, e.g. p = 4: Z takes 7, Y 2; Y takes 3, Z 4; Y takes 5, Z 6). Z's round-start debts are ≤ 1 + min R. `hyb2_states 8`: in the real game at every a ∈ [2p − 1, 4p], p ≤ 8, no Y round start reached against Hyb2 allows a two-pick turn and Z secures ≥ 0 in both roles. `hyb2_states 7 hyb2 thresholds`: Hyb2 draws from a = 2p − 1 exactly (p ≥ 3; 1, 2 for p = 1, 2), as the ideator found; below it the last pair goes to Y in one turn. The step-wise closure of "c(R) ≤ e ≤ 2p − 1 + min R" fails over arbitrary R (`scratch/b20/hyb2_closure.py`, e.g. R = {0,1,2,3}, e = 3, Y takes 2: the only valid answer is 3, e' = 4), so a proof needs the structure of the reachable states.
**Candidate for (a)** (2026-10-26): the potential W, now node L25 with its full proof; refuter in claim mode on W running.
**Lean, tool for (a)** (2026-10-26, `CatchUp/CostParity.lean`). L25's tools (A), (B), kernel-checked: `matchCost_eq_card_odd` (for even O with elements ≤ M, c(O) = #{x < M : an odd number of elements of O are ≤ x}) and `matchCost_erase_two` (for i < j in O: c(O − {i, j}) + 2·#{x ∈ [i, j) : odd} = c(O) + (j − i)). `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.
**Correction to (b)** (2026-10-26; folded into the proof above). The formalized L22 (`valueAux_transfer`) needs every offset < a; at a = 2p − 1 the top offset 2p − 1 equals a, so (b) as written gives a ≥ 2p. In its proof `o < a` only keeps the answerer clear of the early-loss rule (2a ≥ a + i), for which o ≤ a suffices; relaxed in Lean (2026-10-26, L22's section), so (b) holds at a ≥ 2p − 1 given (a).
Refuter, proof mode (2026-10-26): SURVIVES. Checked: Y taking max R first leaves an always-max play in L15's sense (case P1); "first switch" covers post starts reached without an earlier switch; both roles and both parities; the last round's exact tie is a draw in both games and the early-loss rule never hits Z wrongly; a ≥ 2p − 1 suffices (Z debts ≤ 2p − 1 ≤ a, Y's ≤ a + min R, offsets ≤ a) and is tight (Hyb2 loses at 2p − 2, p ≥ 3). Its own literal `valueAux` port (reproduces A278587, n ≤ 12) plays Hyb2 in the real game: Z ≥ draw in both roles for p ≤ 7, every a ∈ [2p − 1, 6p], no round-structure break (`scratch/refuter/l24/`). Applied: KZ, KY and `hendZ` named, offsets ≤ a, L20's partner step cited. For Lean: (c) rests on L15 (paper proof, history-dependent potential); the refuter's route around it is AM+T before the switch (on an exact tie answer the second largest), which keeps L25's T2 and lets L23's formalized classes replace L15; that variant draws in the real game at a ∈ [2p − 1, 2p + 2], p ≤ 7. Free corollary it checked (p ≤ 7, a ∈ [2p − 1, 6p]): with Y moving first, V ≠ win at every debt d ≤ p, d ≡ p (mod 2) (toward L17).

**Lean** (2026-10-26, `CatchUp/Hyb2.lean`): `block_row_draw_hyb2` (rows: the mover trailing by any d ≤ p with d ≡ p (mod 2) draws, from any base score) and `block_draw_hyb2` (d = p mod 2); `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound; tests in `Tests/BlockDrawHyb2.lean` (for p even it is Catch-Up on the block; it implies `block_draw_linear`). Deviations from the paper proof:
- Hyb2's fallback is AM+T's answer (Lean `hyb2Reply`), not always max(R − {i}); they differ only when Y took max R at an exact tie (the refuter's route; T2 holds unchanged).
- (c) uses L23's formalized classes (`KZc`, `KYc`, `closeZ`, `closeY`) before the switch instead of L15.
- (b): KZ, KY are explicit classes, not the reachable starts: `HZw`, `HYw` (offsets of the block, parity (C2), L23's class before the switch or e ≥ c after, W ≤ 2p − 1), closed round by round (`hz_step_w`, `hy_step_w`).
- Z's debts are bounded by d ≤ 2p − 1 directly (a new Z debt is at most Y's pick), not via W or 7 (iv).

## L25 Hyb2's debt bound
**Proof** (L24 ideator, 2026-10-26, from its sketch; every step checked by hand 2026-10-26). No step relies on numerics. Steps tagged [steps: …] were also checked numerically by `scratch/ideator/l24/steps.py` (part 8); the end claim by `wcheck.py`.

Kernel-checked facts cited, not reproved (`lean/CatchUp/CostParity.lean`): CatchUp.matchCost_eq_card_odd (the parity form of c) and CatchUp.matchCost_erase_two (the removal formula).

**Idea in one paragraph.**
- The debt Y would reach by "climbing" every pair above the lowest one is Ψ₂ = e + c − o₂. A climb is Y taking a pair's bottom while Z must answer its top.
- After the switch, e + c never rises, so Ψ₂ never rises.
- A climb needs a gap between pairs larger than half the slack σ = e − c. When the slack exceeds the holes between pairs (τ > η), the structural cap Ψ takes over. Ψ falls when a round removes the min or the max. Otherwise Hyb2's minimal answer cuts Ψ₂ by at least the excess slack.
- Before the switch, every round removes max R (Z takes it, or Y did), so Ψ falls. The switch round lands below Ψ because Z's answer is the first valid one.

**1. Setting**

**Rounds game** (blueprint L13; Lean roundsValue, roundsMargin).
- A round start is s = (R, d, M): R a finite set of naturals with |R| even, M ∈ {Z, Y} the mover, d ∈ ℕ the mover's debt (the mover trails by d). If R = ∅ the game is over.
- Otherwise the mover picks i ∈ R, then the other player picks j ∈ R − {i}. Let δ = d + j − i ∈ ℤ and R' = R − {i, j}.
- If δ ≥ 0, the next round start is (R', δ, M): a tie keeps the mover. If δ < 0, it is (R', −δ, other player).

**Plays.** The start is R₀ = {0, 1, …, 2p − 1}, p ≥ 1, debt g₀ = p mod 2, with either Z or Y as the mover. Z follows Hyb2; Y plays arbitrarily.

**Hyb2.**
- Z as the mover: Z picks max R.
- Z as the answerer, after Y (the mover, debt e) picked i: call j ∈ R − {i} *valid* if e + j − i ≥ c(R − {i, j}), an inequality of integers with c as in part 2. Z answers the **smallest** valid j. If no j is valid, Z answers as AM+T on R − {i} (L23), the *fallback*: max(R − {i}), except on an exact tie e + max(R − {i}) = i with numbers left over, where it answers the second largest of R − {i}.
- This matches solver/src/bin/hyb2_states.rs (offsets scanned in increasing order; dy + j − last ≥ cost(mask − j), else top(mask)).

**Phases of a Y round start (R, e, Y).** Put σ = e − c(R) ∈ ℤ. The start is *pre* (before the switch) if σ < 0 and *post* if σ ≥ 0. Z round starts are not classified.

**2. Notation for a set R**

R is finite with |R| = 2k ≥ 2 and elements o₁ < o₂ < … < o_{2k}.

- Pairs (L20's bottom-up matching): P_t = {b_t, u_t} with b_t = o_{2t−1} (bottoms) and u_t = o_{2t} (tops), t = 1..k.
- g_t = u_t − b_t ≥ 1 (t = 1..k), and h_t = b_{t+1} − u_t ≥ 1 (t = 1..k−1).
- c(R) = Σ_{t=1}^{k} g_t, which is matchCost R; c(∅) = 0.
- η(R) = Σ_{t=1}^{k−1} (h_t − 1) ≥ 0, which is 0 when k = 1. These are the holes between pairs.
- o₂(R) = u₁ is the second smallest element. min R = b₁, max R = u_k, span(R) = u_k − b₁.
- **Ψ(R) = 2·span(R) − |R| + 2 − o₂(R).**
- At a Y round start (R, e, Y): X = e − min R, σ = e − c(R), λ = e + c(R), and **Ψ₂ = e + c(R) − o₂(R) = λ − o₂(R)**. When σ is even and ≥ 0, put τ = σ/2.
- Parity function: π_R(x) = |{r ∈ R : r ≤ x}| mod 2.
- For x ≤ y: O_R(x, y) = |{z : x ≤ z < y, π_R(z) = 1}| and E_R(x, y) = (y − x) − O_R(x, y).
- For s ≤ r: H(s, r) = Σ_{q=s}^{r−1} h_q, which is 0 when s = r.

**3. Tools**

**(A) Zones.**
- π_R(z) = 1 iff b_t ≤ z < u_t for some t. Reason: |{r ≤ z}| = m exactly when o_m ≤ z < o_{m+1}, and this is odd iff m is odd.
- Call [b_t, u_t) the *odd zones* and [u_t, b_{t+1}) (t ≤ k − 1) the *even zones*.
- For x < y both in R, [x, y) is the disjoint union of the zones between consecutive elements of R from x up to y. So O_R(x, y) is the sum of g_t over the odd zones inside [x, y), and E_R(x, y) is the sum of h_t over the even zones inside it. In particular:
  - (A1) For t < r: E(b_t, b_r) = E(u_t, b_r) = H(t, r) and E(b_t, u_r) = E(u_t, u_r) = H(t, r). Also E(b_r, u_r) = 0.
  - (A2) For r ≤ s: O(b_r, u_s) = Σ_{q=r}^{s} g_q and E(b_r, u_s) = H(r, s). For r < s: O(u_r, u_s) = Σ_{q=r+1}^{s} g_q and E(u_r, u_s) = H(r, s). For s < r: O(b_s, b_r) = Σ_{q=s}^{r−1} g_q.
  - (A3) span(R) = c(R) + Σ_t h_t = c(R) + η(R) + (k − 1). The odd zones are disjoint subintervals of [b₁, u_k), so c(R) ≤ span(R).
- Lean matchCost_eq_card_odd: c(R) = |{x < M : π_R(x) = 1}| for every bound M ≥ max R. This is the zone statement summed. [steps: tool:parity-form, tool:c<=span]

**(B) Removal formula** (Lean matchCost_erase_two). For i < j both in R: c(R − {i, j}) = c(R) + (j − i) − 2·O_R(i, j). Removing i and j flips π on [i, j) and nowhere else. [steps: tool:removal]

**(C) Parity.**
- (C1) c(R) ≡ ΣR (mod 2), since Σ_t (u_t − b_t) ≡ Σ_t (u_t + b_t).
- (C2) Every round start (R, d, M) of a play from the start has d + ΣR even. At the start, g₀ + p(2p − 1) ≡ p + p ≡ 0. A round gives δ + ΣR' = d + ΣR − 2i, and −δ ≡ δ.
- (C3) Hence σ = e − c(R) is even at every Y round start that satisfies (C2). [steps: tool:sigma-even]
- The Claim in part 4 is stated for all round starts satisfying (C2), reachable or not.

**(D) Ψ.**
- (D1) Ψ(R) = 2(c + η) − o₂, by (A3): 2·span − 2k + 2 = 2(c + η). [steps: tool:Psi=2(c+eta)-o2]
- (D2) Let R' = R − {x, y} with |R'| ≥ 2. Then max R' ≤ max R and min R' ≥ min R. Also o₂(R') ≥ o₂(R), because R' has at most one element below o₂(R), namely o₁(R). Since |R'| = |R| − 2:
  Ψ(R') − Ψ(R) = 2(max R' − max R) − 2(min R' − min R) + 2 − (o₂(R') − o₂(R)).
  So **Ψ(R') ≤ Ψ(R) whenever the removed pair contains max R** (then max R' ≤ max R − 1) **or min R** (then min R' ≥ min R + 1). [steps: tool:Psi-drops-min/max, tool:o2-monotone]

**(E) The min identity.** At a Y round start with σ even:
Ψ(R) − Ψ₂ = 2(c + η) − o₂ − (e + c − o₂) = 2η − σ.
So for σ ≥ 0, with τ = σ/2: **min(Ψ₂, Ψ(R)) = Ψ₂ − 2·max(0, τ − η)**. It equals Ψ₂ if τ ≤ η, and Ψ(R) if τ > η. [steps: tool:min-identity]

**(F) One Y round.** Y (the mover, debt e) picks i and Z answers j ≠ i. Put R'' = R − {i, j}, e'' = e + j − i, σ'' = e'' − c(R'') and λ'' = e'' + c(R''). By (B):
- (F1) If j > i: σ'' = σ + 2O_R(i, j) and λ'' = λ + 2E_R(i, j).
- (F2) If j < i: σ'' = σ − 2E_R(j, i) and λ'' = λ − 2O_R(j, i).

j is valid iff σ'' ≥ 0. Consequences for the next round start:
- If j is valid and R'' ≠ ∅, then e'' = σ'' + c(R'') ≥ 0, so δ = e'' ≥ 0. The next start is the Y start (R'', e'', Y), and it is post.
- If j is not valid and δ ≥ 0, the next start is (R'', e'', Y) with σ = σ'' < 0, so it is pre.

**4. The potential and the claim**

For a round start s = (R, d, M) with R ≠ ∅:
- **W(s) = Ψ(R)** if M = Z, or if M = Y and σ < 0.
- **W(s) = max(X, min(Ψ₂, Ψ(R)))** if M = Y and σ ≥ 0.

**Claim.** Let s = (R, d, M) satisfy |R| ≥ 4 and (C2), and let Z follow Hyb2. For every choice of Y in the round (Y's pick if M = Y, Y's answer if M = Z), the next round start s' satisfies W(s') ≤ W(s). Its set R' = R − {i, j} has |R'| ≥ 2.

If |R| = 2, the round empties R and ends the game. No round start follows, so nothing is claimed.

**5. Hyb2's answers**

**5.1 Before the switch: Y moves at σ < 0, so σ ≤ −2 by (C3)**

- **(P1)** No j < i is valid: by (F2), σ'' = σ − 2E ≤ σ < 0.
- **(P2)** If i = max R, no j is valid (there is no j > i). So Z uses the fallback, j = o_{2k−1} (or o_{2k−2} on AM+T's exact tie).
- **(P3)** Suppose some j is valid, and let i ∈ P_r. Then the smallest valid j is a top u_s, with s ≥ r if i = b_r and s ≥ r + 1 if i = u_r. Moreover, either b_s = i, or b_s > i and b_s is not valid, that is, σ + 2O_R(i, b_s) < 0, hence σ + 2O_R(i, b_s) ≤ −2 by evenness.

  *Proof.*
  1. Valid j are > i by (P1).
  2. Let b_t > i be a bottom. Then t ≥ 2, and the element of R just below b_t is u_{t−1} ≥ i.
     - If u_{t−1} = i: O(i, b_t) = 0, since [u_{t−1}, b_t) is an even zone. So σ'' = σ < 0, and b_t is not valid.
     - If u_{t−1} > i: u_{t−1} ∈ R − {i}, u_{t−1} < b_t, and O(i, u_{t−1}) = O(i, b_t). So u_{t−1} is valid whenever b_t is.
     In both cases a bottom is never the smallest valid answer. So the smallest valid j is a top u_s > i.
  3. The element of R just below u_s is b_s, and b_s ≥ i because i ∈ R and i < u_s. If b_s ≠ i, then b_s ∈ R − {i} and i < b_s < u_s, so b_s is not valid by minimality.
  4. u_s > i gives s ≥ r when i = b_r, and s ≥ r + 1 when i = u_r. ∎

  [steps: T3:j>i, T3:j-is-top, T3:b_s=i-or-invalid]

**5.2 After the switch: Y moves at σ ≥ 0, τ = σ/2**

- **(Q1)** Every j > i is valid, since by (F1) σ'' ≥ σ ≥ 0. A j < i is valid iff E_R(j, i) ≤ τ, by (F2).
- **(Q2)** Hyb2's answer is exactly one of the following:
  - **(Bt)** i = u_r (any r): j = b_s with s = min{s ≤ r : H(s, r) ≤ τ}. Here s = r is allowed: then j = b_r, the partner.
  - **(Bb)** i = b_r with r ≥ 2 and h_{r−1} ≤ τ: j = b_s with s = min{s ≤ r − 1 : H(s, r) ≤ τ}.
  - **(C)** ("climb") i = b_r with r = 1, or with r ≥ 2 and h_{r−1} > τ: j = u_r.

  *Proof.*
  1. By (A1), for t < r both b_t and u_t have E(·, i) = H(t, r); for i = u_r, also E(b_r, u_r) = 0 = H(r, r).
  2. H(t, r) is nonincreasing in t. So the valid j < i are exactly the elements below i of the pairs P_t with t ≥ s, where s is the least index with H(s, r) ≤ τ. The smallest of them is b_s.
  3. For i = u_r, j = b_r is valid, so a valid j < i exists: case (Bt).
  4. For i = b_r, the elements below i are those of P₁..P_{r−1}. The largest is u_{r−1}, with E = h_{r−1}. So a valid j < i exists iff r ≥ 2 and h_{r−1} ≤ τ: case (Bb), with s ≤ r − 1.
  5. Otherwise no j < i is valid. By (Q1), the smallest valid j is the smallest element of R above b_r, which is u_r: case (C). ∎

  [steps: T4:answer-Bt, T4:answer-Bb, T4:answer-C]
- **(Q3)** The answer is valid. So if R'' ≠ ∅, the next round start is a post Y start, by (F). [steps: T4:next-is-post]
- **(Q4)** Effects of the round (k ≥ 2, R'' = R − {i, j}):

  | Move | e'' | X'' | λ'' | Ψ₂'' |
  |---|---|---|---|---|
  | (C), r ≥ 2 | e + g_r | X + g_r (min R and P₁ unchanged) | λ (F1: E(b_r, u_r) = 0) | Ψ₂ |
  | (C), r = 1 | e + g₁ | X − h₁ < X (min R'' = b₂ = b₁ + g₁ + h₁) | λ | < Ψ₂ (o₂'' = u₂ > o₂) |
  | (Bt) | e − (u_r − b_s) | < X (min R'' ≥ min R) | λ − 2Σ_{q=s}^{r} g_q (F2, A2) | ≤ Ψ₂ − 2Σ_{q=s}^{r} g_q |
  | (Bb) | e − (b_r − b_s) | < X | λ − 2Σ_{q=s}^{r−1} g_q | ≤ Ψ₂ − 2Σ_{q=s}^{r−1} g_q |

  The Ψ₂'' bounds use o₂'' ≥ o₂ (D2). So **Ψ₂'' ≤ Ψ₂ always, and X'' > X only for (C) with r ≥ 2.** [steps: T4:Psi2-monotone, T4:climb-X, T4:X-not-up]

**6. The transitions**

Throughout, s = (R, d, M) satisfies |R| = 2k ≥ 4 and (C2). s' is the next round start, with set R'; |R'| = 2k − 2 ≥ 2.

Every round is one of the following five. A Z start gives T1. A pre Y start gives T2 or T3, depending on whether Y's pick has a valid answer. A post Y start gives T4a or T4b, depending on whether τ ≤ η.

**T1. Z moves (debt d)**

Z picks u_k = max R. Y answers any y ∈ R − {u_k}. Then δ = d + y − u_k, R' = R − {u_k, y}, and W(s) = Ψ(R).

- **δ ≥ 0** (the next start is Z's, at δ), **or δ < 0 with a pre Y start next**: W(s') = Ψ(R') ≤ Ψ(R) by (D2), since the max is removed.
- **δ < 0 with a post Y start next** (e' = u_k − y − d ≥ c(R')): W(s') = max(X', min(Ψ₂', Ψ(R'))) ≤ max(X', Ψ(R')).
  - Ψ(R') ≤ Ψ(R) as above.
  - X' = e' − min R' ≤ (u_k − b₁) − b₁, since y ≥ b₁, d ≥ 0 and min R' ≥ b₁.
  - By (D1) and (A3), Ψ(R) − (u_k − 2b₁) = span − 2k + 2 − g₁ = c + η − k + 1 − g₁ = Σ_{t=2}^{k} (g_t − 1) + η ≥ 0.
  - So X' ≤ Ψ(R), and W(s') ≤ W(s).

This covers every answer of Y (y = min R, y = o_{2k−1}, …) and every d ≥ 0. Parity is not used. [steps: T1:Psi-drops, T1:X'<=Psi(R), T1:W'<=W, for every d, no parity assumption]

**T2. Y moves at σ < 0, and Y's pick i has no valid answer (the fallback)**

Z answers AM+T's j. The removed pair contains max R: if i ≠ max R then j = max R (no tie: e + max R > i), and if i = max R then i itself is removed. W(s) = Ψ(R).

The next start:
- If δ = e + j − i ≥ 0, it is (R', δ, Y), which is pre because j is not valid (F). So W(s') = Ψ(R').
- If δ < 0, it is a Z start, and W(s') = Ψ(R').

Either way W(s') = Ψ(R') ≤ Ψ(R) by (D2).

This covers Y taking max R (always this case, by P2) and Y taking min R when b₁ has no valid answer (then Z answers max R). [steps: T2:max-removed, T2:Psi-drops, T2:next-Y-is-pre]

**T3. The switch: Y moves at σ < 0, and i has a valid answer**

By (P3), Z answers j = u_s, where i ∈ P_r and s ≥ r (i = b_r) or s ≥ r + 1 (i = u_r). W(s) = Ψ(R). Put O = O_R(i, u_s) and E = E_R(i, u_s).

- **(a) Values.** By (A2):
  - if i = b_r: O = Σ_{q=r}^{s} g_q and E = H(r, s);
  - if i = u_r: O = Σ_{q=r+1}^{s} g_q and E = H(r, s).

  In both cases O_R(i, b_s) = O − g_s: the odd zone [b_s, u_s) is the only part of [i, u_s) outside [i, b_s). When b_s = i, both sides are 0.
- **(b) (\*)** e ≤ c − 2(O − g_s) − 2. By (P3), σ + 2(O − g_s) ≤ −2; when b_s = i this reads σ ≤ −2, true because σ < 0 is even. And e = σ + c. [steps: T3:(*)]
- **(c) (\*\*)** E − O + g_s ≤ η + 1, and E − O + g_s ≤ η when i = b_r.
  - If i = b_r: E − O + g_s = Σ_{q=r}^{s−1} (h_q − g_q) ≤ Σ_{q=r}^{s−1} (h_q − 1) ≤ η.
  - If i = u_r: E − O + g_s = Σ_{q=r}^{s−1} h_q − Σ_{q=r+1}^{s−1} g_q ≤ Σ_{q=r}^{s−1} h_q − (s − 1 − r) = 1 + Σ_{q=r}^{s−1} (h_q − 1) ≤ 1 + η.

  [steps: T3:(**)]
- **(d) The next start.** R' = R − {i, u_s}, e' = e + (u_s − i) = e + O + E, σ' = σ + 2O ≥ 0 (valid), and λ' = λ + 2E (F1). Since |R'| ≥ 2, the next start is the post Y start (R', e', Y) by (F), and W(s') = max(X', min(Ψ₂', Ψ(R'))). [steps: T3:next-is-post]
- **(e) Ψ₂' ≤ Ψ(R).**
  Ψ₂' = e + c + 2E − o₂(R')
  ≤ 2c + 2(E − O + g_s) − 2 − o₂(R')  by (\*)
  ≤ 2c + 2η − o₂(R')  by (\*\*)
  ≤ 2c + 2η − o₂(R) = Ψ(R)  by (D2), (D1).
  [steps: T3:Psi2'<=Psi(R)]
- **(f) X' ≤ Ψ(R).** X' = e + O + E − min R' ≤ c − O + E + 2g_s − 2 − min R' by (\*). Hence
  Ψ(R) − X' ≥ c + 2η + 2 − o₂ + min R' − (E − O + g_s) − g_s ≥ c + η + 1 − o₂ + min R' − g_s, by (\*\*).
  - If s ≥ 2: c − g_s ≥ g₁ (pairs 1 and s differ) and min R' ≥ b₁ = o₂ − g₁. So Ψ(R) − X' ≥ η + 1 > 0.
  - If s = 1: then r = 1 and i = b₁, since i = u_r would force s ≥ 2. So R' = R − P₁ and min R' = b₂ = o₂ + h₁. Hence Ψ(R) − X' ≥ (c − g₁) + η + 1 + h₁ > 0.

  [steps: T3:X'<=Psi(R)]

Hence W(s') ≤ max(X', Ψ₂') ≤ Ψ(R) = W(s).

This covers Y taking min R with a valid answer (r = 1, with s = 1 the partner u₁ or s ≥ 2), Y taking a top u_r (s ≥ r + 1), and Y taking a bottom answered by its own partner (s = r: O = g_r, E = 0).

**T4. Y moves at σ ≥ 0 (after the switch)**

By (Q2) the answer is (Bt), (Bb) or (C). By (Q3) the next start is post, so W(s') = max(X', min(Ψ₂', Ψ(R'))). By (E), W(s) = max(X, Ψ₂) if τ ≤ η, and W(s) = max(X, Ψ(R)) if τ > η.

**T4a: τ ≤ η.**
- W(s') ≤ max(X', Ψ₂').
- By (Q4), Ψ₂' ≤ Ψ₂ ≤ W(s).
- X' ≤ X ≤ W(s), except for (C) with r ≥ 2. There X' = X + g_r ≤ X + (c − g₁) = e − b₁ + c − g₁ = Ψ₂ ≤ W(s), because r ≠ 1 gives g_r ≤ c − g₁.

So W(s') ≤ W(s). [steps: T4a:climb<=Psi2]

**T4b: τ > η, i.e. τ ≥ η + 1.**
- **No climb at r ≥ 2.** It would need h_{r−1} > τ ≥ η + 1, but h_{r−1} − 1 ≤ η. So X' ≤ X by (Q4). [steps: T4b:no-climb-at-high-slack]
- It remains to show min(Ψ₂', Ψ(R')) ≤ Ψ(R).
- **The round removes min R or max R.** Then Ψ(R') ≤ Ψ(R) by (D2). This covers:
  - (C) with r = 1 (Y takes b₁);
  - (Bt) with s = 1, and (Bb) with s = 1 (Z takes b₁);
  - (Bt) with r = k (Y takes u_k = max R).

  [steps: T4b:Psi-drops]
- **Otherwise** the move is (Bt) with 2 ≤ s ≤ r ≤ k − 1, or (Bb) with 2 ≤ s ≤ r − 1.
  - (Bb) never removes max R (b_s < b_r < u_r), and removes min R only if s = 1.
  - Since s ≥ 2 is minimal, H(s − 1, r) > τ. Also H(s − 1, r) = (r − s + 1) + Σ_{q=s−1}^{r−1} (h_q − 1) ≤ (r − s + 1) + η. Hence **τ − η ≤ r − s**.
  - (Bt): Ψ₂' ≤ Ψ₂ − 2Σ_{q=s}^{r} g_q ≤ Ψ₂ − 2(r − s + 1) < Ψ₂ − 2(τ − η) = Ψ(R), by (E).
  - (Bb): Ψ₂' ≤ Ψ₂ − 2Σ_{q=s}^{r−1} g_q ≤ Ψ₂ − 2(r − s) ≤ Ψ₂ − 2(τ − η) = Ψ(R).
  - (In T4b, (Bt) with s = r ≥ 2 cannot occur, since it needs h_{r−1} > τ. The argument does not use this.)

  [steps: T4b:interior-s>=1, T4b:tau-eta<=r-s, T4b:Psi2'<=Psi(R)]

So W(s') ≤ max(X, Ψ(R)) = W(s).

In T4, Y taking max R is (Bt) with r = k, and Y taking min R is (C) with r = 1 (Z answers u₁). Both are covered in T4a and T4b. [steps: T4:W'<=W]

All five round types are covered. ∎

**7. Consequences for L24 (a)**

- **(i) Start value.**
  - Z first: W = Ψ({0..2p−1}) = 2(2p − 1) − 2p + 2 − 1 = **2p − 1**.
  - Y first at g₀ = p mod 2: c({0..2p−1}) = p (pairs {2t − 2, 2t − 1}), so σ = g₀ − p.
    - For p ≥ 2, σ < 0 and W = Ψ = 2p − 1.
    - For p = 1, σ = 0 and W = max(1 − 0, min(1 + 1 − 1, 1)) = 1 = 2p − 1.
  - So W = 2p − 1 at both starts.
- **(ii)** Every round start of a play from the start satisfies (C2) by (C). By the Claim and induction on rounds, every round start with R ≠ ∅ of a play consistent with Hyb2 has W ≤ 2p − 1.
- **(iii) Y round starts.**
  - If σ ≥ 0: e − min R = X ≤ max(X, …) = W ≤ 2p − 1.
  - If σ < 0: e < c(R) ≤ span(R) ≤ 2p − 1 − min R, by (A3) and R ⊆ {0..2p−1}. So e < 2p − 1 − min R ≤ 2p − 1 + min R.
  - Hence **every Y round start has e ≤ 2p − 1 + min R**, which is L24 (a)'s bound for Y. (At pre starts also X < Ψ(R) = W, since c − b₁ ≤ 2c + 2η − b₁ − g₁. This is not needed.)
- **(iv) Z round starts.** These are outside W's claim; this is all that L24 (b) needs.
  - At a start Z's debt is g₀ ≤ 1.
  - After a Z round with δ ≥ 0, Z's new debt is δ = d + y − u_k < d, since y < u_k.
  - After a Y round, Z becomes the mover only if δ = e + j − i < 0. Valid answers exclude this (F), so it happens only after a fallback (T2) with i = max R and j ∈ {o_{2k−1}, o_{2k−2}}. Z's debt is then u_k − j − e ≤ span(R) ≤ 2p − 1.
  - Hence Z's round-start debts are ≤ 2p − 1 ≤ a + min R for a ≥ 2p − 1.
  - L24 (a)'s stronger "Z's debt ≤ 1 + min R" is **only measured** (p ≤ 10: Z's debt is always 0 or 1, reach.py), not proved here. (b) does not use it.
  - Side remark on (b): at a = 2p − 1 the max offset equals a. The transfer needs "≤ a" rather than "< a": the answerer's shortfall i − j − d ≤ i ≤ 2p − 1 ≤ a ≤ a + min R'.

**8. Checks and scope**

- **steps.py 11 12** checks every tagged step above, on every R within {0..11} with |R| even and every debt up to c(R) + 12. Parity (C2) is imposed wherever the proof assumes it; T1 is checked for every debt. All hold.
  - In steps.py, pair indices are 0-based: (Q2) r, s are one less than here; r − s is unchanged.
- **steps.py 13 10** runs the same checks on every R within {0..13}, debts up to c + 10. All hold, for example T3: 126,261 switch rounds; T4: 342,972 post rounds; T1: 139,741 rounds into a post start. Output: steps-13-10.txt.
- **wcheck.py exh 13 16** checks the Claim itself: 196,590 round starts within {0..13}, both movers, every debt up to c + 16 with (C2), 0 rises. wcheck.py rand: 80,000 random starts of span 50, 0 rises.
- **whole.py reach 10** covers every reachable round start for p ≤ 10: W(start) = 2p − 1, σ is always even, no rise.
- **Mutations that break the claim** (wcheck.py mut):

  | Mutation | Rises |
  |---|---|
  | drop the η term (W = max(X, Ψ₂) after the switch) | 156 |
  | Hyb's partner answer | 19,242 |
  | largest valid answer instead of smallest | 62,585 |
  | Ψ − 1 | 2,653 |

  So the tie-break "smallest valid j" and the exact constant are used.
- **Not covered:**
  - starts violating (C2), i.e. odd σ;
  - the real game (that is L24 (b), via L22's proof);
  - Z's "≤ 1 + min R" (see 7 (iv)).
- **Naming.** Ψ here is Ψ_η in the ideator's report. The report's "+ (σ mod 2)" term is 0 under (C2).
**Evidence.** Refuter, claim mode (2026-10-26, own Rust engine and a literal Python port, `scratch/refuter/l24w/`): HOLDS. No rise of W over every even R with |R| ≥ 4 inside a span of 26 (shift-invariant), both movers, every debt of the right parity up to c + 20 (1.14·10⁹ round starts, 1.43·10¹⁰ transitions); span ≤ 21 up to c + 100; sparse sets (|R| ≤ 6 within {0..40}, |R| = 4 within {0..60}); 4·10⁶ random sets; every reachable start for p ≤ 13 (start value 2p − 1, bounds (a) hold, Z's debt ≤ 1). Sharp points, all as stated: the switched side must be e ≥ c(R) (e > c fails at the p = 3 start); "valid" must be ≥ (> fails); o₂ is the second smallest element itself (o₂ − min R fails); the parity hypothesis is needed. Mutations: no η term, Hyb's partner answer, largest valid answer, Ψ − 1 each break it.
Refuter, proof mode (2026-10-26): SURVIVES. Every step checked by hand; cases complete (five round types, Z's answer kinds complete by (Q2), T4b's min/max-removing moves exactly listed); both Lean tools used as stated. Its own literal code (π by counting, Hyb2 by brute force, `scratch/refuter/l25/steps_ref.py`) asserts 58 intermediate claims, 0 failures: every R ⊆ {0..15} containing 0 with debts ≤ c + 16 (3.34·10⁶ transitions), ⊆ {0..16} with debts ≤ c + 8 (5.0·10⁶), ⊆ {0..10} with debts ≤ c + 60, 21,500 random sets within {0..60}; every branch reached. At odd σ exactly the steps marked as using parity fail. Applied its two wording fixes (part 7 (iii), (iv)). For Lean: the zone facts (A1), (A2) need their own lemmas; the Claim covers all starts with even debt + sum, so "R ⊆ {0..2p−1}, parity, W ≤ 2p − 1" is a class closed under Hyb2's rounds.

**Lean** (2026-10-26, `CatchUp/Hyb2.lean`): `potW_z_round` (T1) and `potW_y_round` (T2–T4, split as `potW_y_round_fallback`, `potW_y_round_switch`, `potW_y_round_post`) for every T with |T| ≥ 4 and (C2) (T1 without parity), `potW` being W and `psi_range` the start value 2p − 1; `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound. Deviations from the paper proof:
- The fallback is AM+T's answer (see part 1); T2 is unchanged.
- Index-free zones: no pair indices; bottoms and tops are elements with `OddBelow` true or false, `oddPts`/`evenPts` count O and E, and η counts even holes (the points of [min R, max R) outside R with π = 0), which equals Σ(h_t − 1).
- T4 is split by the side of the answer (j < i: (Bt), (Bb); j > i: (C)) and then by τ ≤ η, not T4a/T4b first. In (Bt)/(Bb) at τ > η the bound τ − η ≤ r − s comes from q, the element just below j (u_{s−1}, a top that is not valid), and (Bt) with r = k needs no separate case. (C) at i = min R uses that the min is removed; at i ≠ min R the slack is low, so W = max(X, Ψ₂) and X'' ≤ Ψ₂.

## L26 Token lemma
**Statement.** R a finite set of naturals, t = min R, s any score. If the mover trailing by t on R − {t} draws, `valueAux (R.erase t) s (s + t) false = .draw`, then the level mover on R draws: `valueAux R s s b = .draw` for b = true (opening) and b = false.
**Proof.** At scores (s, s) any single pick ends the turn, so with either flag the mover's options are, for each x ∈ R, neg(A_x) with A_x = `valueAux (R.erase x) s (s + x) false` (the opponent's node).
- x = t: A_t is the hypothesis node, a draw, so this option is a draw.
- x > t: the opponent may take t first. Since t < x it stays strictly behind, so that option of A_x is Q_x = `valueAux ((R.erase x).erase t) (s + t) (s + x) false`. In the hypothesis game the mover (score s, opponent s + t) may pick x > t (x ∈ R − {t}), which ends its turn; that option is neg(Q_x) on the same set ((R − x) − t = (R − t) − x) with the same scores. The hypothesis node is not empty (it holds x) and not an early loss (that would be a loss, not a draw), so its value is the best of its options. The hypothesis game is a draw, so by L6 none of its options is a win: neg(Q_x) ≠ win, so Q_x ≠ loss. If the early-loss rule fired at A_x (s + sum(R − x) < s + x), then (s + t) + sum(R − x − t) < s + x too, so Q_x = loss (or, if R − x − t is empty, the scores s + t < s + x give loss); hence the rule does not fire and A_x = best of its options ⊇ {Q_x}, so A_x ≠ loss by L6, and neg(A_x) ≠ win.
- So some option is a draw and none is a win: the value is a draw (L6). No "depends only on the deficit" lemma is needed, since Q_x has the same scores in both games.
**Evidence.** Ideator (2026-10-26, unchecked, `scratch/ideator/fresh/` and `scratch/ideator/descent/token.rs`): every S ⊆ {2..18} with V(S, 1) = draw (58,811 sets) gives value({1} ∪ S) = draw, and the tie-position form holds in all 107,840 cases within {1..18}. On {1..N} opening 1 draws for every even-total N ≤ 35 (data), so the converse holds there.

## L27 Two block families suffice
**Statement.** If V({1..2p}, 0) = draw for every even p ≥ 2 and V({2..2p+1}, 1) = draw for every odd p ≥ 1, read at score s = 0 (`valueAux … 0 0 false`, `valueAux … 0 1 false`), then L1.
**Proof.** 1 + … + N is even iff N ≡ 0 or 3 mod 4. N ≡ 0 mod 4, N = 2p with p even: value({1..N}) = V({1..N}, 0) (the opening flag changes nothing at a level start, `valueAux_true_eq_false`), the first family. N ≡ 3 mod 4, N = 2p + 1 with p odd: {2..N} is the block a = 2 with 2p numbers, its g0 = p mod 2 = 1, a draw by the second family; L26 with R = {1..N}, t = 1, s = 0 gives value({1..N}) = draw. (N = 0 is trivial.)
**Lean (2026-10-26).** `CatchUp.token_lemma` (L26): `t ∈ R`, `∀ x ∈ R, t ≤ x`, `valueAux (R.erase t) s (s + t) false = .draw` ⊢ `valueAux R s s false = .draw`; the opening flag via `valueAux_true_eq_false` (moved from the tests into `Token.lean`). `CatchUp.conjecture_of_two_families` (L27): `(∀ N, N % 4 = 0 → valueAux (Icc 1 N) 0 0 false = .draw) → (∀ N, N % 4 = 3 → valueAux (Icc 2 N) 0 1 false = .draw) → Conjecture`, with `even_triangle_iff` (1 + … + N even ⇔ N ≡ 0, 3 mod 4). `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound. Deviations: L27's hypotheses are indexed by N (N % 4 = 0, 3, N = 0 included, where {1..0} is empty) instead of by p, and read at score 0, as the refuter advised; L26 is stated for the non-opening flag, the opening flag following from `valueAux_true_eq_false`; the early-loss cases go through `valueAux_early_loss`.
**Meaning.** The N ≡ 3 mod 4 half of the conjecture needs TI only at height 2, not 1; before, TI at height 2 gave only "player 1 does not lose" (L10 (a)).
**Refuter.** Proof mode (2026-10-26), L26 and L27: SURVIVES. Checked against `valueAux` case by case: both opening flags at the level node, x = t, A_x non-empty and no early loss, the hypothesis node reaching its option list, Q_x the same call in both games (no deficit lemma used), t = 0, \|R\| = 1; L27's mod-4 bookkeeping and N = 0, 3. Its own literal port (`scratch/refuter/l26/token.rs`): all nonempty R ⊆ {0..17}, 109,998 satisfying the hypothesis, all level draws, every intermediate claim holds; the ideator's 58,811 and 107,840 reproduced; value({1..N}) matches A278587 for N = 3..19. Fixes applied (x > t; non-emptiness; erase commutation; hypotheses read at s = 0). Side observations, unchecked beyond {0..15}: the conclusion also held with the token at any rank, and whenever a level option is a draw no level option is a win. Literature: no reduction relating {1..N} to {2..N} found. For N ≡ 0 mod 4, L26 also gives L1(N) ⟸ V({2..N}, 1) = draw (an odd-count block), so both halves can be posed at height 2.

## L28 Level law
**Statement.** R finite, t ∈ R (any rank), s any score. If `valueAux (R.erase t) s (s + t) false = .draw`, then `valueAux R s s b = .draw` for either opening flag b. Equivalently: at a level position, if some pick draws then no pick wins.
**Proof.** As in L26, the level mover's options are neg(A_y) with A_y = `valueAux (R.erase y) s (s + y) false`; y = t gives a draw. Let y ≠ t; the opponent answers t.
- y > t: the opponent stays strictly behind (s + t < s + y): its option is Q_y = `valueAux ((R − y) − t) (s + t) (s + y) false`, which is neg of the hypothesis game's option "pick y" (that pick ends its mover's turn, s + y ≥ s + t). As in L26, Q_y ≠ loss, A_y is not an early loss, so A_y ≠ loss.
- y < t: the opponent catches up (s + t ≥ s + y), so its option is neg(P_y) with P_y = `valueAux ((R − y) − t) (s + y) (s + t) false`, the level mover now trailing by t − y. In the hypothesis game the mover's pick y leaves it strictly behind (s + y < s + t), so that option is P_y itself, on the same set ((R − t) − y = (R − y) − t) with the same scores. The hypothesis node is not empty (it holds y) and not an early loss (that would be a loss), so it is the best of its options; it is a draw, so P_y ≠ win (L6), so the opponent's option neg(P_y) ≠ loss. A_y is not empty (it holds t) and not an early loss (its numbers sum to at least t > y). So A_y ≠ loss.
- In both cases neg(A_y) ≠ win; with the draw at y = t the value is a draw (L6). Minimality of t is never used; L26 is the special case.
**Consequence.** value({1..N}) = draw iff some opening t of {1..N} leaves player 2 drawing at deficit t: one good opening suffices, at any rank. The refuter's observation on L26 (all R ⊆ {0..15}: whenever a level option draws, none wins) is the s = 0 case of the "Equivalently" form.
**Stronger form (same argument, not used).** For y ≠ t the opponent after y does at least as well as the negation of the hypothesis node after t; so at a level position at most one pick wins, and if one does, every other pick loses (refuter: 0 violations over all R ⊆ {0..17}; it fails at trailing nodes, e.g. R = {1, 3} behind by 2).
**Lean (2026-10-26).** `CatchUp.level_law` (`CatchUp/Token.lean`): `t ∈ R`, `valueAux (R.erase t) s (s + t) false = .draw` ⊢ `valueAux R s s false = .draw`; the opening flag via `valueAux_true_eq_false`; `token_lemma` (L26) is now its corollary. `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound. No deviation from the paper proof beyond the non-opening flag.
**Refuter.** Proof mode (2026-10-26): SURVIVES. Every case checked against `valueAux` (y = t, y > t as in L26, the new y < t case with its turn bookkeeping, t = 0, y = 0, R = {t}); exhaustive tests with its own literal and deficit ports: all R ⊆ {0..11} at four scores and every t (19,688 hypothesis triples, every proof step asserted), all R ⊆ {0..17} at every rank; value({1..N}) matches A278587 for N = 3..20 and every even-total N ≤ 20 has a drawing opening. Wording fixes applied. Literature: Feng (2024) proves P2 cannot win at a tie with 3 or 4 numbers left, a different statement; nothing like the level law found.

## L29 One family at height 2
**Statement.** If `valueAux (Icc 2 N) 0 1 false = .draw` for every N ≥ 2 with 1 + … + N even, then L1.
**Proof.** N = 0: no numbers, a draw. N = 1: odd total, nothing to prove. N ≥ 2: value({1..N}) = `valueAux (Icc 1 N) 0 0 false` (`valueAux_true_eq_false`), and L26 with R = {1..N}, t = 1, s = 0 needs exactly `valueAux (Icc 2 N) 0 1 false = .draw`, since {1..N} − {1} = {2..N}.
**Necessity (data, not proved).** Opening 1 draws for every even-total N ≤ 35 (results; N = 33–35 from one engine), so no member of the family fails there. In general the family is equivalent to L1 iff opening 1 draws whenever {1..N} draws, which is open: L1(N) gives only some drawing opening (L28).
**Evidence.** Two-pick class (`turn_cap ranges 2 18 1 2 2`): the defender draws {2..N} at deficit 1 for every even-total N ≤ 16 with both players' turns ≤ 2 picks.
**Lean (2026-10-26).** `CatchUp.conjecture_of_height_two` in the strict build, standard axioms; no deviation.
**Refuter.** Proof mode (2026-10-26): the implication SURVIVES (N = 0, 1, 2 and both residues checked; the Lean hypothesis matches). The first wording of "Necessity" was wrong (for N ≥ 12 every opening draws only for even totals; L1 does not give opening 1), corrected above.

## L30 Two-token lemma
**Statement.** R finite, s any score, t ≠ y in R. If `valueAux (R.erase t) s (s + t) false ≠ .win` (after the level mover's t the opponent cannot win), then `valueAux (R.erase y) s (s + y) false ≠ .loss` (after its y the opponent does not lose). Corollary: if two distinct picks t, t' each leave the opponent unable to win, the level position is a draw.
**Proof.** L28's copying argument with the weaker hypothesis. Let H = `valueAux (R.erase t) s (s + t) false` (opponent to move, trailing by t) and A_y the opponent's node after y.
- If H is an early loss (s + sum(R − t) < s + t), then y ≤ sum(R − t) < t. A_y is not an early loss (it holds t > y), so it reaches its options; its option t catches up and ends the opponent's turn, after which the level mover trails by t − y with everything left summing to sum(R − t) − y < t − y: a loss for it (early loss, or the terminal rule if nothing is left). So A_y = win, in particular ≠ loss.
- Otherwise H holds y, so it is nonempty and the best of its options, none of which is a win (H ≠ win, L6). y < t: as in L28, the opponent's t at A_y reaches the level mover at the very call P_y that is H's option "pick y" (same set, same scores), P_y ≠ win, so A_y ≠ loss. y > t: the opponent's t keeps it behind and reaches Q_y, whose negation is H's option "pick y", so Q_y ≠ loss; A_y is not an early loss (else Q_y would be a loss), so A_y ≠ loss.
- Corollary: each option of the level mover is neg(A_y). With t and t' both "opponent cannot win", every option y ≠ t is ≠ win (by t) and the option t is ≠ win (by t', since t ≠ t'); the option t is ≠ loss (hypothesis), so it is a draw; the value is a draw (L6). In outcome terms (win 1, draw 0, loss −1), applying the lemma to (t, y) and to (y, t) gives m_y + m_t ≤ 0 for the level mover's options y ≠ t: at most one pick wins, and then every other pick loses.
**Lean (2026-10-26).** `CatchUp.level_option_ne_loss` (the lemma) and `CatchUp.two_token` (the corollary) in `CatchUp/Token.lean`, stated for the non-opening flag; `level_law` (L28) is now proved from `level_option_ne_loss`. `lake build --wfail` clean; axioms propext, Classical.choice, Quot.sound.
**Refuter.** Proof mode (2026-10-26): SURVIVES; three wording gaps fixed above (the terminal rule in the early-loss case, A_y reaching its options, H holding y). t ≠ t' is needed: R = {1, 2}, s = 0 is a win although pick 2 leaves the opponent an early loss. Own literal port (`scratch/refuter/l30/`): every R ⊆ {0..13}, s ∈ {0, 1, 3, 7}, every t ≠ y, each step asserted (907,256 cases); deficit port on every R ⊆ {0..22}: 0 violations.
**Evidence.** Ideator (2026-10-26, `scratch/ideator/review3/`): 98.8% of drawn level sets within {1..20} have at least 2 non-losing openings, every drawn interval does. Lean draft `scratch/ideator/review3/lean/TwoTokenSmall.lean` compiles (`two_token`, `level_option_ne_loss`; standard axioms).

## L31 One-sided roots
**Statement.** (a) If for every N ≥ 4 with 1 + … + N even, `valueAux ((Icc 1 N).erase 1) 0 1 false ≠ .win` and `valueAux ((Icc 1 N).erase 2) 0 2 false ≠ .win`, then L1. (b) If for every such N, `valueAux (Icc 2 N) 0 1 false ≠ .win` and `valueAux (Icc 3 N) 1 2 false ≠ .win`, then L1.
**Proof.** N ≤ 3: N = 0 is empty, N = 1, 2 have odd totals, N = 3 is L30 with the picks 1 and 3 ({2, 3} at deficit 1 and {1, 2} at deficit 3 are not mover wins, by direct evaluation). (a) For N ≥ 4: L30 with t = 1, t' = 2 at the opening (opening flag via `valueAux_true_eq_false`). (b) For N ≥ 4: by L29 it suffices that V({2..N}, 1) = draw. The first hypothesis gives ≠ win. For ≠ loss: the mover's pick 2 on {2..N} (trailing by 1) ends its turn ahead by 1, so that option is neg(`valueAux (Icc 3 N) 1 2 false`), which is ≠ loss by the second hypothesis. N = 3 for L29 directly ({2, 3} at deficit 1 is a draw).
**Meaning.** Both forms ask only "the player to move does not win" from two starts: a strategy proof needs one role, the leader's defense, not two. Data (ideator): (a) holds for every even-total N ≤ 35 (every opening draws for N ≥ 12; N = 4, 7, 8, 11 by table); (b) holds for N ≤ 24.
**Lean (2026-10-26).** `CatchUp.conjecture_of_leader_pair` (a), `CatchUp.conjecture_of_suffix_pair` (b, via L29; it does not need L30), `CatchUp.conjecture_le_three` (L1 for N ≤ 3) in `CatchUp/Token.lean`; strict build, standard axioms; hypotheses use the goal's parity expression `Even (N * (N + 1) / 2)`. No deviation.
**Refuter.** Proof mode (2026-10-26): SURVIVES. N ≤ 3 checked; the hypotheses fail at N = 3 (so N ≥ 4 is needed); (a) and (b) hold for every even-total N from 4 to 24 (own port; the ideator's N ≤ 35 for (a) not rechecked).

## L32 TI at real heights
**Statement.** B(h, p) = {h + o : 0 ≤ o < 2p}, h real, the mover trailing by g0 = p mod 2 (same units). Draw for every h > 0 (p even), every h ≥ 1/2 (p ≥ 3 odd), every h ≥ 1 (p = 1). Scaling by 1/δ is an isomorphism, so equivalently an arithmetic progression of 2p terms, first term a, difference δ, the mover trailing by g0·δ, is a draw for a/δ in the same ranges. At h = 1 and p even this is L1 for N = 2p; at h = 2, p odd, it is L27's second family.
**Why the parameter helps.** Every comparison in the game is (difference of pick counts)·h + integer, with the count difference at most 2p, so the game's combinatorial type is constant between consecutive fractions r/s with s ≤ 2p, and constant for h > p(2p − 1) + 1 (L13). At a generic h a draw is a balanced split: both players take p numbers, with offset sums equal (p even) or differing by the debt. Crossing a breakpoint h* changes the tree only at near-tie nodes: a player ε behind continues, or ε ahead hands the move over; both are the same position (R, ε) with the roles swapped, so the root can change only through near-tie positions that are not draws (at generic h, every position with |R| odd is one).
**Evidence.**
- Refuter, claim mode (2026-10-26, `scratch/refuter/tir/`): an exact parametric solver (`param.rs`, h symbolic; checked against {1..N} at h = 1 for N ≤ 14 and against an integer solver on 31k random comparisons) gives the value as a function of h on all of (0, ∞): draw everywhere for p = 2, 4, 6, 8; for p = 1 a mover win on (0, 1), draw from 1; for p = 3, 5, 7 a mover win on (0, 1/2), draw from 1/2. Integer engines agree at every breakpoint and cell midpoint up to h = p(2p−1) + 3 for p ≤ 7. p = 9: draw at all breakpoints in [1/2, 3] and the grid j/19 on [9/19, 20]; p = 10: draws on (0, 1] exhaustively and the grid j/23 on (0, 3].
- The odd threshold falls below 1/2 for larger p (refuter): 2/5 at p = 9 (mover win exactly on (0, 2/5) among 613 points on (0, 3]), 1/3 at p = 11 (one engine). So for p odd the statement claims only h ≥ 1/2; the true threshold θ_p ≤ 1/2 is not part of it.
- Ideator (`scratch/ideator/fresh/genbreak.rs`, `genscan.rs`): every breakpoint and a grid hitting every cell on (0, 2p + 1] for p ≤ 7; p = 8 breakpoints (mine, `scratch/b45/`): all 1,360 draws.
- Openings (refuter, exact): the second smallest opening draws on (0, ∞) for p = 2, (0, 8) for p = 4, (0, 11) for p = 6; the smallest on (0, 2), (0, 6), (0, 9). With L30 (two drawing picks at a tie), "the opponent cannot win after the two smallest openings" would give L32 for p even below those heights.
- Literature: nothing on Catch-Up over arithmetic progressions or real numbers (refuter, four searches; mine, two).

## L33 Sign lemma
**Statement.** For every finite S and g ≥ 0: V(S, g) = sign(m(S, g)), where m(S, g) is the margin game's value for the mover trailing by g (same moves and turn hand-overs as Catch-Up; no early-loss rule: a mover who cannot catch up keeps taking numbers; payoff the mover's final score minus the opponent's; both players optimize it). m is defined on finite multisets (a pick removes one copy); the proof works there unchanged. V uses the non-opening flag; the opening flag only differs at g > 0, and value(S) = V(S, 0) (L13's section, `valueAux_true_eq_false`).
**Proof.** Same move sets and the same hand-overs. Terminal positions agree in sign: S = ∅ gives sign(−g) for both; a Catch-Up early loss (sum(S) < g) is a margin-game line where the mover takes everything and ends at sum(S) − g < 0, and every line from there ends there. sign is non-decreasing and odd, so it commutes with max and with negation; induction on |S|.
**Evidence.** Refuter (2026-10-28, `scratch/refuter/mt/`): 119,626 (S, d), multisets included, d up to sum + 3: early-loss value, play-out value and sign(m) agree; V({1..N}) for N ≤ 18 reproduced. Margins on {1..N} at a tie are 0 (even total) or ±1 (odd) for N ≤ 16 (`scratch/a10/mrows.rs`).
**Refuter.** Claim mode (2026-10-28): the argument is correct. Proof mode (2026-10-28): SURVIVES (S = ∅, early loss with its strict test, the general step; a line-by-line Python port of `valueAux` agrees with sign(m) on every subset of {0..11}, g from −2 to sum + 3, two base scores: 319,488 checks; multisets: 385,924 checks); wording fixed above (the flag, multisets).

## L34 Far blocks are a margin tolerance
**Statement.** S a finite set of positive integers, E_k = k 4-blocks {x_i..x_i+3}, x_1 > 2·sum(S) + 10, each later block above twice the total below it plus 10. Then m(S ∪ E_k, g) = sign(m)·max(|m| − 2k, |m| mod 2), m = m(S, g), i.e. ψ applied k times, ψ(X) = X − 2·sign(X) for |X| ≥ 2 and X for |X| ≤ 1. With L33: if sum(S) + g is even, V(S ∪ E_k, g) = draw iff |m(S, g)| ≤ 2k (MT); if odd, V(S ∪ E_k, g) = sign(m(S, g)).
**Position form (k = 1).** m(S ∪ Q, d) = ψ(m(S, d)) for every S below a far quadruple Q and every d ≤ max S; for a far pair it fails exactly where the low game ends level (who moves next matters), the quadruple's own row being 0 at a tie. ψ is monotone and odd on each parity class, so playing Q last commutes with optimal play: the content is that opening Q early never helps. Route to a proof: induction on |S|; the S-picks give ψ(m(S, d)) exactly; an early opening of Q leaves a far pair after the reply, which needs the pair's turn-dependent form.
**Use.** FB (k = 1): a drawn set stays drawn with a far 4-block on top. A6's Lemma B (the low game with the top quadruple as final payoff) is L34 for {1..N−4}, so it follows from L1(N − 4).
**Evidence.**
- Recorded run: [results/far-block-margin.md](results/far-block-margin.md) (`far_block_margin`, committed): the position form for k = 1 on every S ⊆ {1..14} and k = 2 on {1..10}, d ≤ u, 0 failures, after reproducing `Solver` as sign(m) with the blocks intact.
- Mine (2026-10-28, `scratch/a10/farblock.rs`, `mtplus.rs`): MT on every even-sum S ⊆ {1..13}, k ≤ 2; the position form on every S ⊆ {1..10}, d ≤ 10.
- Refuter, claim mode (2026-10-28, `scratch/refuter/mt/`): MT on all even-sum S ⊆ {1..16} (k ≤ 2) and {1..17} (k = 1), {1..13} for k ≤ 4, 3,000 random sparse sets (k ≤ 4), large-element sets, 181 sets with m = −4, −6; gaps 1–4, 7; spacings far, 2B + 11 + random, 7B + 3. The margin form on all S ⊆ {1..12} (k ≤ 1), {1..10} (k ≤ 2), {1..8} at g = 3. The spacing can be weakened to x ≥ (total below) − 6 on {1..13}; a block just above max S fails ({5, 6, 7}, k = 1).
**Refuter.** Claim mode (2026-10-28): SURVIVES.

## L35 Sliding quadruple (Const)
**Statement.** For N ≡ 0, 3 (mod 4), N ≥ 4, V({1..N−4} ∪ ({N−3..N} + c), 0) is the same for every integer c ≥ 0.
**Refuter.** Claim mode (2026-10-28): SURVIVES (no non-draw; the ideator's checks stopped below T(N) at N = 16, 23, 24, now covered except N = 24 between samples and c ≤ 60 at N = 23, 24).
**Use.** L1(N) ⇐ L1(N − 4) ∧ FB({1..N − 4}) ∧ L35(N): for c large the moved quadruple is a far block over {1..N − 4} (L34's spacing), which draws by L1(N − 4) and FB; L35 carries that value to c = 0. Bases N = 0, 3 (L1 directly); N = 4 uses FB(∅). At c = 0 L35 is L1(N) itself, so the reduction helps only through a proof uniform in c (refuter). A10's earlier chain over k far blocks is not needed, and for k ≥ 1 it was ill-defined (the moving quadruple can hit a far block's numbers).
**Band form.** For every M ≤ 16, c ≤ 30 and every d ≤ M with d ≡ sum{1..M} (mod 2): m({1..M} ∪ ({M+1..M+4} + c), d) = ψ(m({1..M}, d)), which is 0 (a draw) for M ≥ 6; at odd-margin entries a ±1 changes sign with c (`scratch/a10/rowconst.rs`). Position-wise the band fails on sparse sets, rarely on dense ones (`nearq.rs`: all subsets of {1..12} with ≥ 10 numbers pass; QB, "a quadruple above a band-drawn set keeps its band", fails 8 of 1,858 times, `qb.rs`).
**Evidence.** Recorded run: [results/slide-quad-n20.md](results/slide-quad-n20.md) (`slide_quad`, committed, `Solver` at every integer c ≤ T(N) + 1, N ≤ 20, with O19 as a control): no non-draw. Refuter, claim mode (2026-10-28, `scratch/refuter/a10/`, own engine reproducing A278587): every comparison is j·c + b with |j| ≤ 4, |b| ≤ T(N) = 1 + … + N, so the value is constant for c > T(N); draw at every integer c for N ≤ 20 (to T(N) + 20), N = 23 for c ∈ [61, 278], N = 24 at 22 sampled c ∈ [61, 301]; every real c for N ≤ 16 (breakpoints in (1/12)ℤ, grid 1/24); one defender strategy in both roles for every integer c at N ≤ 16 and every real c at N = 8, 11, 12 (`robust.rs`). The interval base is needed (O19). Ideator (2026-10-26, `scratch/ideator/review5/deform*.rs`): no non-draw for N ≤ 16 (c ≤ 120), N = 19, 20 (c ≤ 400), N = 23, 24 (c ≤ 60; the only check below c = 61 there); one c-uniform defender strategy for N = 8, 11, 12, 15, 16 (c ∈ [0, 30] ∪ {500}). Mine: N = 19 with one far block, 21 shifts; c-uniform strategies at N = 7, 8 (`scratch/a10/uniform.py`): the defender grabs low numbers before taking a quadruple number, no evident rule. Not a proof route: closing an opened pair at once, or within the next turn, loses (O18).

## L36 Twins with a tie-break (TD's first cell)
**Statement.** For p ≥ 1 and B = {1, 3, …, 2p − 1} (fam a) or {2, 4, …, 2p} (fam b): the multiset of pairs {x, x + ε}, x ∈ B, with 0 < ε < 1/(p + 1) and the mover trailing by ε·(p mod 2) (not the opening), is a draw. Every such ε gives the same game, the lexicographic one (integer parts first, then the count of upper elements). At ε = 0 it is exact twins, a draw by peeling the top twins (log 2026-10-22).
**Use.** The base of A11: L1 for N = 2p (fam a, p even) and N = 2p + 1 (fam b, p odd, via L29) follows from L36 and TD's crossings of the breakpoints r/s, s ≤ p + 1, up to t = 1.
**Evidence.** Mine (2026-10-28, `scratch/a11/twineps.rs`): draw for fam a p ≤ 11, fam b p ≤ 10. Refuter (2026-10-28, `scratch/refuter/td/tdlex.rs`, exact limit game): draws at TD's own deficit; the limit game is not unit-token Catch-Up at other deficits; completing the opponent's broken pair loses from p = 3 (P1) and p = 4 (P2), and P1 must open low. Not all bases: 12 of about 6,500 sets B ⊆ {1..14} with |B| ≤ 6 fail, all with a sparse high core ({7, 8, 10, 11, 12}).

## L37 Gap bound (LG)
**Statement.** S a finite multiset of positive integers, d ≥ 0, m the margin game (L33). γ(W) = the largest gap between consecutive elements of sorted W ∪ {0} (repeated elements give 0; γ({1..N}) = 1; γ(∅) = 0). LG: m(S, d) ≥ −γ(S ⊎ {d}): the player to move never loses by more than the largest gap of the numbers left, its deficit counted as one more number. G (tie form): |m(S, 0)| ≤ γ(S).
**Reductions (paper, refuter pending).** (1) LG ⇒ G: the lower half is LG at d = 0; for the upper half, every opening x hands the opponent (S − x, x) with (S − x) ⊎ {x} = S, so A(S, x) ≥ −γ(S) and no opening is worth more than γ(S). (2) G ⇒ LG: for d = 0, LG is G's lower half (γ(S ⊎ {0}) = γ(S)); for d ≥ 1, at a tie on T = S ⊎ {d}, opening d is worth −m(S, d) ≤ m(T, 0) ≤ γ(T); this uses G on multisets (T has a repeat when d ∈ S). (3) G({1..N}) ⇒ L1(N): |m| ≤ 1; every play takes all numbers, so the final margin has the parity of the total (m(S, g) ≡ sum(S) + g mod 2), hence m = 0 for an even total, and V = sign(m) = draw (L33). Refuter, proof mode (2026-10-28): (1)–(3) SURVIVE; fixes applied (γ(∅) = 0, the clause d = 0).
**Why it is different.** It is a statement about every position, so an induction has its hypothesis everywhere and needs no family closed under play (O5, O7, O11, O18), and nothing local about one position (O4, O8, O20). Catch-Up as differencing: a pick x replaces {d, x} in V = S ⊎ {d} by |d − x|, the new deficit; always-max self-play is greedy number partitioning, whose discrepancy is at most γ(V) (ideator, own derivation); LG says the trailer keeps that bound against an adversary. Obstruction sets satisfy it with big gaps (O10's set: γ = 75; {2,2,2,3,3} wins by exactly γ = 2).
**Open part.** A proof: the two-ply induction "a move after which every reply keeps γ ≤ γ(root)" fails at intervals (taking a middle number makes γ = 2), so it needs an amortized potential, as L15 and L25 did.
**Evidence.** Ideator (2026-10-28, `scratch/ideator/stall28/`, unchecked): 0 violations on every S ⊆ {1..22}, d ≤ 22 (96.5M positions); every S ⊆ {1..12}, d ≤ 30; multisets over {1..7} (multiplicity ≤ 3) and {1..10} (≤ 2); about 18M random positions with values to 1000 and generic ties to 10⁶; O7's 232 cores with all sub-multisets; sparse pair families; O2, O3, O10, O15. Tight at singletons, at ({a, b, a + b}, d = a) when a < b ≤ 2a, and at odd-total intervals (|m| = 1). Recorded run: [results/gap-bound-u22.md](results/gap-bound-u22.md) (`gap_bound`, committed; 0 violations on every S ⊆ {1..22}, d ≤ 22, after reproducing `Solver` as sign(m)). Mine (2026-10-28, `scratch/a12/lgcheck.rs`, own table): 0 violations on every S ⊆ {1..20}, d ≤ 20 (22.0M positions); G at every tie; interval margins 0 or ±1 to N = 20, matching the known signs. Refuter, claim mode (2026-10-28, `scratch/refuter/lg/mse.rs`, dense table over sub-multisets, matched against three other solvers and A278587): SURVIVES, 0 violations of LG or of either half of G in about 80 billion positions: every S ⊆ {1..27}, d ≤ 27 (3.76G); multisets with high multiplicities ({1, 2} up to 60 copies, …, {1..16} doubled); deficits past the total; one big gap with dense parts on both sides; O10's set translated and doubled; O7's whole five-pair family with max ≤ 44 and every sub-position (13.3G), and with {1, 2} added (33.4G); two-scale compositions; perturbations of the tight cases; hill-climbing (sets of distinct values peak at |m|/γ = 0.974, multisets stall at 1 on twin-built shapes); generic values to 10⁶ (both halves). Interval margins: |m({1..N}, 0)| = 1 at N = 21, 22, 25, 26, 0 at 23, 24, 27, and m({1..N}, d) ≥ −1 for every d ≤ N ≤ 27. Losing at a tie by exactly γ within {1..21}: exactly {1..9}, {1..10}, {1..14}, {1..18}, 2·{1..9}, 2·{1..10}, {2, 4, …, 16, 17, 19}. The ideator's "O7 cores with all sub-multisets" had no saved run behind it (`lgfam2.rs` skips the cores; `lgfam.rs` checks only full sets), and `lgtie.rs` checks only G's lower half; the refuter's sweeps cover both.

## L38 Margin two-token lemma
**Statement.** S a finite multiset, a tie (the mover to move, d = 0). For x ∈ S let A(S, x) = m(S − x, x), the opponent's value after the opening x, so m(S, 0) = max over x of −A(S, x). For openings of distinct values y < t: A(S, t) + A(S, y) ≥ 0.
**Proof.** Let Z = m(S − {t, y}, t − y). After the opening t the opponent, trailing by t, may take y (y < t keeps it behind by t − y, so it moves on) and reaches (S − {t, y}, t − y) as the mover: A(S, t) ≥ Z. After the opening y the opponent, trailing by y, may take t (t > y catches up and leads by t − y), which hands the opener (S − {t, y}, t − y): A(S, y) ≥ −Z. Add.
**Consequences.** (i) If an opening wins by w > 0, every opening of another value loses by at least w (a margin form of L30). (ii) If two openings x1 ≠ x2 (distinct values) have A(S, x_i) ≤ γ(S), then G holds at S: the lower half from x1; for the upper half, A(S, x) ≥ −A(S, x1) ≥ −γ(S) for x ≠ x1 and A(S, x1) ≥ −A(S, x2) ≥ −γ(S).
**Limit of (ii).** On multisets with repeats two safe openings need not exist although G holds: {2, 2, 5, 5} (γ = 3, A(2) = 0, A(5) = 4, m = 0), {3, 3, 7, 7}, {4, 4, 4, 9, 13}, {6, 6, 14, 17}; 12 multisets over {1..8} with multiplicities ≤ 2 (refuter). Equal values are excluded from the lemma (the copy hands over at a tie). So G on multisets, which reduction (2) of L37 needs, cannot come from (ii) alone. No set (without repeats) lacks two safe openings: none within {1..18}, none in 20,000 random sets.
**Evidence.** Ideator (2026-10-28, `mtwotoken.rs`): all 10,027,008 opening pairs with S ⊆ {1..18}; every S ⊆ {1..18} with at least two elements has two safe openings. Refuter: multisets over {1..6} (multiplicity ≤ 3) and {1..8} (≤ 2), 110,538 pairs; 20,000 random sets and multisets; 0 failures.
**Refuter.** Proof mode (2026-10-28): SURVIVES, with (i) and (ii); |S| = 2 gives exactly 0; both deficits in the proof are positive, so no exact-tie hand-over occurs.
