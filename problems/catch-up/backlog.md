# Backlog

Grouped by line, most promising first.

## A2

- **B2 A class whose defects may grow.** Fixed hole bounds don't close (O5). Candidates: broken adjacent pairs ≤ ⌈N/6⌉ (holds the whole game for N ≤ 24); defects weighted by height or by the gap they cost; "paired above k, anything below". Test each with `hole_game` (cost = numbers left).
- **B10 Hole game beyond N = 24.** To see whether adjacent defects grow like N/6: a boolean "can D keep ≤ h broken pairs all game" table at 2 bits per position, layered and parallel, for N = 27, 28 (~2 GB).
- **B5 Endgames in Lean.** Formalize L7 (paper proof; statement shape in its section) via a membership form of `valueAux` (using L6); then three numbers left, cross-checked against Feng's case analysis (README, Known).

## A3

- **B4 Patch drawing strategies.** `strategy_eval` exists; leaderboard: fixed pick rules (Largest, Smallest, SmallestCatch, Exact, LeadOne, StayBehind) fail at N = 4 as player 1; rules that repair broken adjacent pairs hold N = 3, 4 as player 2 only. Patching fixed rules is aimless; a rule needs a region to steer into (A2) or the opponent's last pick (B9).

## A4

- **B22 Low-change law.** Adding {1..k} below an O7 core C cures it at a sharp k (ideator: 1+…+k ≈ 2·min C). For 40 refuter cores (`scratch/refuter/l8/hunt-E5-31-44.txt`) and random 5–7-pair cores to max 60, find the least k(C) with {1..k} ∪ C drawing at g0 for k(C)..k(C)+3 and fit it against min C. The naive law "S ⊇ {1..k}, max S ≤ 1+…+k ⇒ draw" is false: {1..9} ∪ {25,26,28,29,36,37,39,40,43,44} is a player-2 win, every opening loses (re-solved with `Solver`).
- **B3 Richer density notion.** Completeness nearly characterizes even-sum draws; find what its 523 exceptions with max ≤ 30 lack (`quad_step 30` lists the first). Complete sets fail badly at moderate gaps ({1,2,4,8,16} at gap 5 is a mover win), near-intervals don't (L4). Candidates: few holes relative to max (L4); consecutive numbers differ by ≤ 2; S ⊇ {1..k} with k ≥ max(S)/2.

## A5 (line dead: O7; kept for a revised line on dense pair sets)

- **B14 Odd-p upper bound.** L10 (b) proves "≤ draw" for p even by partner replies; for p odd a bottom pick answered by its partner leaves the mover at gap 2 with an even number of pairs, a mover win in 446 E sets ⊆ {1..28} (smallest {2,3,4,5}). List, for those positions, which defender replies hold the draw and what returns them to a known class (an E or T set at its g0, or L9, L11); the same question for pick 2 in T sets. Tool: `pair_moves`.
- **B12 A closed class around (E, g0).** After the attacker's pick, R has exactly one odd run; find the gaps at which such sets draw and whether the defender can always return to (E, g0) or to that class (ideator: 39,767 of 73,198 drawing picks repairable at U = 20).
- **B13 Margin tool.** Score restricted defenders by the final margin M instead of win/draw/loss; check |M({1..N}, 0)| ≤ 1 to N ≈ 26 (ideator, unchecked).
- **B15 Far-apart pairs without (F).** L9 with F0 (each pair exceeds the sum below) and (A) held on all sets with p ≤ 4, max ≤ 200 (refuter), but (P2) fails under F0; find an induction that claims only what peeling needs (L' = L, g ≤ a_1).

## A6

- **B23 Lemma A along play.** Along the defender's value-keeping play in Γ_N every early opening only turns an attacker loss into a draw (refuter, N ≤ 24). Find the smallest class of positions, closed under that play, on which "early openings never win" holds, and test it to N = 28 with `top_reserve`.
- **B18 Lemma B's payoff on paper.** The row of {a..a+3} at debts below a: draw at 0 and 2, loss elsewhere (a ≥ 5); like L9 (P1).

## A7

- **B19 Rows of translated blocks.** For p ≤ 8, a ≤ 80 (`Solver` per block): TI at g0, the height a0(p) from which the row is t_p, whether the band contains [0, p] at every a.
- **B20 High blocks on paper.** Reduced to the rounds game (log 2026-10-26: high blocks reduce to a rounds game; `scratch/b20/NOTES.md`): prove T1 (rows of {0..2p−1} are t_p; holds p ≤ 12) or T2 (pair sets at debts 0, 1; holds within {0..23}). Done: U0 (debt > c(O) loses), parity. Open: a class closed under play (O10 rules out all sets).
- **B24 Pair sets with owed orphans.** After a non-partner answer two orphans remain, one owed to each player (its partner went to the other). Tabulate R on pair sets plus k ≤ 2 orphan pairs by owner and debt with `rounds_game`, looking for a formula in the split count that would close T2's induction.
- **B21 Margin Lipschitz bound (tool).** M(R, g + 1) ≥ M(R, g) − 1 (ideator: every R ⊆ {1..16}); the naive induction fails at the tie pick x = g ({5,9,11,13,15,19}). Rerun at U = 20, then try a proof.
