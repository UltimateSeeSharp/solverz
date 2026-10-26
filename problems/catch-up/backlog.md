# Backlog

Grouped by line, most promising first.

## A2
- **B31 A regime the same at every height (R1/R2).** The defender restricted to ≤ 2 picks per own turn (R1), or to leaving the opponent < 2·min(left) behind (R2), still draws {1..N} for every even-total N ≤ 24 and blocks p ≤ 7, a ≤ 40 (ideator, unchecked; log 2026-10-26: ideator on A7's descent). A class closed under play is what A2's revival asks for. Blocks p = 8, 9 done (no new exception); five fixed turn rules inside R2 lose at N = 3–4 (log 2026-10-26: the lead regime R2 holds, but no simple rule inside it). Next only with a new idea for describing the drawing turns (e.g. by a potential).

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
- **B20 High blocks on paper.** TI part done: L16 (paper proof, refuter-checked). Left: B26 (all rows t_p), B27 (lower heights), B28 (Lean).
- **B28 Formalize L15, L16.** L13, L14 done (`CatchUp/Rounds.lean`, `CatchUp/AltSum.lean`), and value = sign of the minimax margin with its parity (`CatchUp/Margin.lean`). Next L15 (balanced-start induction; or L18 with L19 once L19 is proved, per-round and easier in Lean), then L16 (parity from L3). L16's statement needs your approval only if reported.
- **B26 AM+T on paper.** AM+T (always-max; as second picker, never answer with an exact tie: take the second largest) meets t_p on {0..2p−1} at every debt in both roles (p ≤ 12) and every T2 target on pair sets within {0..23} (log 2026-10-26: avoiding exact ties gives every row of high blocks). Route: L18 (potential Γ from c_td, step lemma drafted) and L19 (its condition holds along play from pair sets with Z trailing by at most the top run; checked within {0..16}); left: a proof of L19, then the parity-forced cases without the last-round drop. Gives L17 (T1) and T2; supersedes AM+X (B25).
- **B29 Avoid carries (Hyb).** Z plays always-max (AM+T for rows) until Y, as round mover, trails by more than U0's c(R); then U0's partner answers. Round-start debts stay ≤ 3m, so for a > 3m the real game is the rounds game along every play against Hyb, and L15 + U0 give TI at a ≥ 6p − 2 (log 2026-10-26: ideator on A7's descent). Done: L20, L21, L22 paper proofs (refuter-checked). Left: formalize L20 (drafted in `scratch/lean/Matching.lean`); a tighter debt bound (observed 2m − 3) would lower the height.
- **B30 Frugal switch (Hyb2).** As second picker take the smallest answer leaving Y lost by U0, else always-max; the ideator's real-game engine finds blocks drawn exactly from a = 2p − 1 (doubling-free). Next: list Hyb2's real-game states at a ∈ [2p − 1, 4p] with Y trailing by ≥ a and find the invariant that keeps them lost.
- **B27 Lower the height.** In the real game always-max draws blocks at g0 from a = p(p−1) + [p odd] (refuter, p ≤ 8) versus the rounds-game bound 1 + p(2p−1): measure the largest debt along always-max play against a perfect opponent and transfer L15 to multi-pick turns.
- **B21 Margin Lipschitz bound (tool).** M(R, g + 1) ≥ M(R, g) − 1 (ideator: every R ⊆ {1..16}); the naive induction fails at the tie pick x = g ({5,9,11,13,15,19}). Rerun at U = 20, then try a proof.
