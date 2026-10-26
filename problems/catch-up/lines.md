# Lines of attack

Status: `main`, `active`, `shelved` (with reason), `dead` (killed by an obstruction).

## A1: Induction on intervals by peeling pairs (`dead`: O4)

- **Reduction.** If adding a pair {x, x+1} above every remaining number changes a position's value by a fixed rule of its values at gaps g − 1, g, g + 1, then the values on {1..N} follow from those on {1..N−2}, and the conjecture reduces to small cases. Blueprint root: L1.
- **Metric.** Largest universe U (positions with numbers from {1..U}) on which the pair rule holds with no counterexample. Now: fails at U = 2, for windows up to g ± 4, even with x and parity in the key (2026-10-22).
- **Evidence.** Top twins {x, x} do cancel (mirror strategy), but a pair's effect depends on R globally (log 2026-10-22: a top pair does not act locally).
- **Kill criteria.** A counterexample to the pair rule that no extra position feature repairs. Met: O4.

## A2: An invariant region of positions (`shelved`: fixed-bound classes and partner pairing fail closure, O5, O6, and when to refuse the partner has no cheap rule; revive with a class closed under play from A5, B12)

- **Reduction.** For each player P a class C_P of positions (numbers left, gap, P to move) such that: P's first turn start is in C_P (for player 2, after every opening); from each C_P position P has a turn after which every opponent turn returns P to C_P or ends the game without P losing. Then P never loses; with both players, the game is a draw. Blueprint root: L1.
- **Metric.** Violations of that closure for the best candidate class, as the earliest point (numbers left) where the opponent can force P out of it. Now: no fixed-h hole class closes (O5); adjacent pairs with ≤ 2 broken hold until 0–11 numbers are left for N ≤ 24, ≤ 4 broken hold the whole game for N ≤ 24 (2026-10-22).
- **Evidence.** The parity law (L3). Interval rows follow the parity rule exactly in a middle band of gaps; draw-parity gaps are never losses there (log 2026-10-22: interval rows). Near-intervals with few holes keep this (L4, L5); complete sets don't. Drawing play looks like adjacent pairing with defects that grow like N/6 (log 2026-10-22: holes grow under drawing play).
- **Kill criteria.** Every simple candidate C has closure violations growing with N.

## A3: Explicit drawing strategies (`shelved`: fixed pick rules lose at N = 4; a strategy needs a region to steer into)

- **Reduction.** A simple rule for each player that never loses against perfect play, for every even-total N, proves the conjecture once the rule's guarantee is proved.
- **Metric.** First N where the best rule loses against a perfect opponent (leaderboard in B4, higher is better). Now: 4 (2026-10-22).
- **Evidence.** For N ≥ 12 every opening draws, so both players have slack; six greedy rules all lose from N = 4 (log 2026-10-22: fixed pick rules).
- **Kill criteria.** The best rules fail at small N and patching each failure only moves it a few steps. Revive when A2 has a class with tested closure: evaluate "move into the class" with `strategy_eval`.

## A4: A characterization of drawn sets (`shelved`)

- **Reduction.** A property P of sets with P({1..N}) for even-total N and "P and even sum ⇒ draw", proved by induction on sets, gives the conjecture.
- **Metric.** Even-sum sets with max ≤ 30 that have P but don't draw. Now: 523 for P = complete (O3); 0 for P = "near-interval with |H| ≤ 4 and m ≥ 14" (L4).
- **Evidence.** Completeness is almost right (O3); few holes is better (L4).
- **Kill criteria.** Already shaky: P must survive moves, and completeness doesn't (log 2026-10-22). Revive if a refined P (B3) is preserved by play; holes grow with play, which B6 measures.

## A5: Sets made of adjacent pairs (`dead`: O7)

- **Reduction.** Prove L8 (pair sets draw at gap p mod 2; plus {1,2,3} ∪ pairs); it contains L1 at N ≡ 0, 3 mod 4. Try the toy cases first (far-apart pairs, p = 2), then a class closed under play containing (E, g0).
- **Metric.** Largest family of E sets with a paper proof of L8. Now: p ≤ 2 (L7, L11) and far-apart pairs for every p (L9); false from p = 5 (O7; none found for p ≤ 4). Reductions (L10): T ⇐ E for "≥ draw"; for p even, "≤ draw" ⇐ L8 for p − 1; for p odd the partner reply fails (B14).
- **Evidence.** That entry; top twins cancel (mirror, log: a top pair does not act locally).
- **Kill criteria.** A counterexample to L8, or neither far-apart pairs nor p = 2 yields a paper proof. O4 warns that adding a top pair is not a local rule for arbitrary R; O6 that forced partner replies fail.

## A6: Inert top quadruple (`shelved`: Γ_N draws to N = 28, but Lemma A has no local form (O8), so the split fails; revive with an invariant along the defender's play, e.g. "early openings only rescue attacker losses")

- **Reduction.** Γ_N: the defender never takes from Q = {N−3..N} except to close a pair the attacker opened, or when only Q is left. A defender strategy in Γ_N is one in the real game, so L1(N) ⇐ the defender draws Γ_N as player 1 and as player 2. Splits into Lemma A (opening a Q-pair while lower numbers remain never helps the attacker; the dense analogue of L9 (P2)) and Lemma B (the game on {1..N−4} with Q as final payoff: the player to move when {1..N−4} runs out draws at debt 0 or 2, loses otherwise).
- **Metric.** Largest N with Γ_N drawn in both roles: 28 (log 2026-10-22: the top quadruple can wait, but not by a local lemma), then the status of Lemmas A and B (A: false position-wise, O8).
- **Evidence.** Ideator (scratch, unchecked; log 2026-10-22: line review, new lines): Γ_N drawn for every even-total N ≤ 24; reserving 3 or more top pairs loses (N = 12 as P2, 16–24 both); with both players barred from early openings every reserved block of 2–5 pairs draws for N ≤ 20, so Lemma A carries the content. L9 (top pairs act as a final payoff).
- **Kill criteria.** A loss in Γ_N at an even-total N; or Lemma B no easier than L1(N − 4) (the reduction is one step: stacking quadruples loses).

## A7: Even blocks at any height (`active`: revived by you 2026-10-22 for B20, the high-block proof, main until 2026-10-26; high blocks done on paper to a ≥ 2p − 1 (L24), which A8 uses as its high phase; the monotone descent stays blocked by O9)

- **Reduction.** TI: V({a..a+2p−1}, p mod 2) = draw for all a, p ≥ 1. a = 1 with p even is L1 for N ≡ 0 mod 4; a = 2 with L10 (a) gives "player 1 doesn't lose" for N ≡ 3 mod 4. Route: prove TI for large a (debts stay below a or near a, as in L9), then show the draw band does not shrink as a decreases.
- **Metric.** The range of (a, p) with a paper proof of TI: p ≤ 2 at every a (L7, L11); every p at a > 1 + p(2p−1) (L16), at a ≥ 6p − 2 (L21) and at a ≥ 2p − 1 (L24, 2026-10-26, tight for Hyb2); Lean-checked for every p at a ≥ 6p − 2 (`CatchUp.block_draw_linear`, 2026-10-26). Next: the descent below 2p − 1 (O9); Lean for L24 when it pays.
- **Evidence.** High sets are exactly the rounds game (L13, paper proof); there every pair set draws at g0, and always taking the largest number secures it (L15, paper proof); one exception (AM+T) gives every row t_p (checked p ≤ 12) (log 2026-10-26). Ideator (scratch, unchecked): translated even blocks draw at g0 for p ≤ 6, a ≤ 60, while O7's separated pairs fail at the same heights; for a ≥ 12 (p ≤ 6) the row at debts below a is t_p: draw at draw-parity debts ≤ p, loss elsewhere, except a win at debt 0 for p odd.
- **Kill criteria.** A translated even block that is not a draw at g0; or a band that loses part of [0, p] at some height. The descent to a = 1 is the hard part; shelve if the large-a proof gives no handle on it.

## A8: Low phase, high phase (`main` from 2026-10-26: A7's high-block results give the high phase; the data say the low phase is simple)

- **Reduction.** The defender D plays in two phases. Low phase, while the set is low (min < span): D makes change with its k smallest numbers, turns of ≤ 2 picks, and steers into a class H of high positions (min ≥ span, debts and parity as in L25's class). High phase: from every position of H, D draws by Hyb2 (L25's potential W; L24 is the case of full blocks). L1 ⇐ (i) a high-phase lemma for H and (ii) a low-phase lemma: from {1..N} at gap 0, in both roles, D can enter H without losing. Blueprint roots: L24, L25 (high phase).
- **Metric.** Largest N for which (ii) holds with a fixed k and H described explicitly, checked by search; then the nodes of (i) and (ii) at `paper proof`. Now: free low play then Hyb2 from the first high position draws {1..N} to N = 24 ([results/low-high-hyb2-n24.md](results/low-high-hyb2-n24.md)); bottom-4 picks while low (free when high) draw to 24 ([results/low-high-n24.md](results/low-high-n24.md)); H not yet described (2026-10-26).
- **Evidence.** Top picks are needed only on high sets and in endgames (log 2026-10-26: while the set is low, the defender needs only its smallest numbers). Turns of ≤ 2 picks for both players suffice to N = 24 ([results/turn-cap-intervals-n24.md](results/turn-cap-intervals-n24.md)). On high sets every turn is one pick (L13) and Hyb2's potential W never rises (L25, refuter-checked).
- **Kill criteria.** The needed k grows without bound with N at every threshold; or the switch positions D can force admit no class H on which D draws (e.g. Hyb2 or any high strategy loses from positions D cannot avoid).

