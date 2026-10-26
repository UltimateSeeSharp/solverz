# Backlog

Grouped by line, most promising first.

## A2
- **B31 Two-pick game (R1/R2).** D keeping every turn of both players to ≤ 2 picks (opponent behind by ≤ its 2 smallest numbers left) draws {1..N} to N = 24 ([results/turn-cap-intervals-n24.md](results/turn-cap-intervals-n24.md)); for N ≤ 12 also with cap 2m − 1 and inside tb3. Earlier failures at a = 1 came from an engine flaw (log 2026-10-26: two-pick turns for both players suffice). Next: rerun the fixed `lead_regime` (blocks, rules) and look for a potential in the two-pick game, the way W works for the rounds game.

- **B2 A class whose defects may grow.** Fixed hole bounds don't close (O5). Candidates: broken adjacent pairs ≤ ⌈N/6⌉ (holds the whole game for N ≤ 24); defects weighted by height or by the gap they cost; "paired above k, anything below". Test each with `hole_game` (cost = numbers left).
- **B10 Hole game beyond N = 24.** To see whether adjacent defects grow like N/6: a boolean "can D keep ≤ h broken pairs all game" table at 2 bits per position, layered and parallel, for N = 27, 28 (~2 GB).
- **B5 Endgames in Lean.** Formalize L7 (paper proof; statement shape in its section) via a membership form of `valueAux` (using L6); then three numbers left, cross-checked against Feng's case analysis (README, Known).

## A3

- **B35 Low phase, high phase.** While the set is low D needs only its smallest numbers: 2 while max > 3·min, 4 until min ≥ span, for N ≤ 24 ([results/low-high-n24.md](results/low-high-n24.md)); top picks are needed on high sets and in endgames (log 2026-10-26: while the set is low, the defender needs only its smallest numbers). tb3 draws {1..N} to N = 24 ([results/two-ended-intervals-n24.md](results/two-ended-intervals-n24.md)); on blocks the window must grow with p ([results/two-ended-blocks-p9-10.md](results/two-ended-blocks-p9-10.md)). Next: the positions at the switch to high (sets, debts, mover) under drawing low play: does L25's class (offsets ≤ min, parity, W ≤ min) contain them, or can D steer into it? Then whether the needed k stays bounded beyond N = 24 (hash memo).
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

- **B38 Rows at the doubling-free height.** From every row start with d ≤ p, W = 2p − 1 and the start is in L23's class, so Hyb2T secures ≥ −1: every draw entry of t_p at a ≥ 2p − 1 (ideator: both roles, every d ≤ p with d ≡ p, from a = 2p − 1, failing at 2p − 2, p ≤ 7, `scratch/ideator/l24/rows.py`; p = 8, 9 the same, log 2026-10-26: Hyb2T rows hold to p = 9). Next: the refuter in claim mode with its own engine.
- **B39 Pair sets at a ≥ 2m − 2p + 1.** W does not use the interval structure: for a pair set E with min 0, W(start) = 2m − 2p + 1; with L15, L20, L22, E draws at g0 from that height (ideator: all 986 pair sets with p ≥ 2 within [0, 16) in the real game, 463 fail one lower, `pairsets.py`). Would supersede L21's a > 3m. Next: after W's verdict, the refuter in claim mode with its own engine on pair sets within {0..17}.

- **B37 Margin domination on blocks.** For p ≤ 7, a ≤ 50, g ≤ 3p: M(B(a,p), g) ≥ μ(I_p, g), the high block's margin row, except at g = 0 with p odd (p = 5: a = 1, 2, 7; p = 7: a = 1, 5, 7–11) (ideator, unchecked, `scratch/ideator/review2/real_vs_rounds.rs`). One-sided, so O9 (a win) does not contradict it. Next: the same comparison one pick after the start; if it holds, domination + L17 gives "player 1 doesn't lose {1..N}" for N ≡ 0 mod 4. Passed to the descent ideator.
- **B36 Deque Catch-Up (toy).** Every pick the smallest or largest left (positions are intervals). TI holds for p ≤ 12, a ≤ 60, and even-total {1..N} draw to N = 100 (reproduced). Rows (p ≤ 30, lo ≤ 200): all draws at lo ≤ p − 1; exactly "D ≤ p, L ≤ lo, W above" from lo = 3p − 4; mixed between (log 2026-10-26: deque Catch-Up rows have two clean regimes). Next: describe odd lengths and off-parity debts too and check the full description closed under both moves (a proof of deque TI); or drop if the mixed band has no short description.

- **B28 Formalize TI for high blocks.** Done for a ≥ 6p − 2: `CatchUp.block_draw_linear`, rows `block_row_draw_linear`. Next, at a ≥ 2p − 1 without L15: Hyb2T (AM+T before the switch) keeps W (88,048 states within {0..12}; draws blocks from a = 2p − 1 for p ≤ 7, `scratch/ideator/l24/hyb2t.py`); its one new combinatorial fact, c(R − {i, j}) = c + (j − i) − 2O(i, j), is in Lean (`matchCost_erase_two`); Hyb2T's answer rule and "a lost opponent stays lost" drafted in `scratch/lean/Hyb2.lean` (compiles); next, after W's verdict, W's transitions.
- **B26 AM+T on paper.** AM+T meets t_p on {0..2p−1} at every debt in both roles (p ≤ 12) and every T2 target within {0..23}. Draw entries of t_p: L23 (formalized), and for real blocks at a ≥ 6p − 2 `CatchUp.block_row_draw_linear`; losses for d > p: L20; left: the parity-forced entries (B33). L18 + L19 remain the route for spaced pair sets (L19 open; ideator's idea: K's depth sum above the first gap plus L15's credits below it).
- **B33 Parity-forced entries.** W at d = 0 for p odd, L at 1 ≤ d ≤ p with d ≢ p: an analogue of K on odd-parity states with end condition s ≥ 1; four template families failed (counterexample (6,4,3,2,1,0) at s = 1, Y moving, ends at −1). Next: the greatest closed class with target +1 (`scratch/ideator/l19/mono.py`), fit its Z-thresholds in (a1, D_Z, q).
- **B30 Frugal switch (Hyb2).** As second picker take the smallest answer leaving Y lost by L20, else always-max; draws blocks exactly from a = 2p − 1 (L24, paper proof). (a): L25 (paper proof). L24 itself survived proof mode (paper proof). Left for Lean: AM+T before the switch so L23's classes replace L15 (refuter's route, L24 section). (b): done in Lean (offsets ≤ a).
- **B21 Margin Lipschitz bound (tool).** M(R, g + 1) ≥ M(R, g) − 1 (ideator: every R ⊆ {1..16}); the naive induction fails at the tie pick x = g ({5,9,11,13,15,19}). Rerun at U = 20, then try a proof.
