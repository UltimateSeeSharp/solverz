# Lines of attack

Status: `main`, `active`, `shelved` (with reason), `dead` (killed by an obstruction).

## A1: Induction on intervals by peeling pairs (`dead`: O4)

- **Reduction.** If adding a pair {x, x+1} above every remaining number changes a position's value by a fixed rule of its values at gaps g − 1, g, g + 1, then the values on {1..N} follow from those on {1..N−2}, and the conjecture reduces to small cases. Blueprint root: L1.
- **Metric.** Largest universe U (positions with numbers from {1..U}) on which the pair rule holds with no counterexample. Now: fails at U = 2, for windows up to g ± 4, even with x and parity in the key (2026-10-22).
- **Evidence.** Top twins {x, x} do cancel (mirror strategy), but a pair's effect depends on R globally (log 2026-10-22: a top pair does not act locally).
- **Kill criteria.** A counterexample to the pair rule that no extra position feature repairs. Met: O4.

## A2: An invariant region of positions (`main`)

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
