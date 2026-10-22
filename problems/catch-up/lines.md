# Lines of attack

Status: `main`, `active`, `shelved` (with reason), `dead` (killed by an obstruction).

## A1: Induction on intervals by peeling pairs (`main`)

- **Reduction.** If adding a pair {x, x+1} above every remaining number changes a position's value by a fixed rule of its values at gaps g − 1, g, g + 1, then the values on {1..N} follow from those on {1..N−2}, and the conjecture reduces to small cases. Blueprint root: L1.
- **Metric.** Largest universe U (positions with numbers from {1..U}) on which the pair rule holds with no counterexample. Now: untested (2026-10-22).
- **Evidence.** Paper sketch only (B1). Set-level induction by four fails (O1, O2), which is why this works at the level of positions.
- **Kill criteria.** A counterexample to the pair rule that no extra position feature repairs.

## A2: An invariant region of positions (`active`)

- **Reduction.** If a class C of positions (numbers left, gap) contains every even-total opening, the mover in C always has a turn that keeps the opponent in C, and C positions are never losses, then optimal play from {1..N} is at least a draw for both players, hence a draw. Blueprint root: L1.
- **Metric.** Positions in the layered tables (N ≤ 22) that violate the closure conditions for the best candidate C. Now: no candidate yet (2026-10-22).
- **Evidence.** The parity law (L3) and the empirical parity rule: most positions draw exactly where a draw is possible; deviations at gaps ≤ 2 and the largest gaps.
- **Kill criteria.** Every simple candidate C has closure violations growing with N.

## A3: Explicit drawing strategies (`active`)

- **Reduction.** A simple rule for each player that never loses against perfect play, for every even-total N, proves the conjecture once the rule's guarantee is proved.
- **Metric.** First N where the best rule loses against a perfect opponent (leaderboard, higher is better). Now: no evaluator yet (2026-10-22).
- **Evidence.** For N ≥ 12 every opening draws, so both players have slack; a simple rule may exist.
- **Kill criteria.** The best rules fail at small N and patching each failure only moves it a few steps.

## A4: A characterization of drawn sets (`shelved`)

- **Reduction.** A property P of sets with P({1..N}) for even-total N and "P and even sum ⇒ draw", proved by induction on sets, gives the conjecture.
- **Metric.** Even-sum sets with max ≤ 30 that have P but don't draw. Now: 523 for P = complete (O3).
- **Evidence.** Completeness is almost right (O3).
- **Kill criteria.** Already shaky: P must survive moves, and completeness doesn't (log 2026-10-22). Revive if a refined P (B3) is preserved by play.
