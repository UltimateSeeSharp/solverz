# Backlog

Grouped by line, most promising first.

## A2

- **B9 When must the defender refuse the partner?** Drawing play looks like adjacent pairing, but an unconditional partner reply loses from N = 11 (O6), even at one broken pair and gap 3. In the forced-partner game (reference: refuter's `scratch/refuter/partner/forced2.mjs`), list for N ≤ 20 the positions reached where the partner loses but another pick draws, and find what separates them (sum left against the gap, as in the Win tail of the interval rows; broken pairs; phase). A rule "partner unless P" is then evaluated in that game, not by per-position rates (log 2026-10-22: answering with the partner is not a strategy).
- **B2 A class whose defects may grow.** Fixed hole bounds don't close (O5). Candidates: broken adjacent pairs ≤ ⌈N/6⌉ (holds the whole game for N ≤ 24); defects weighted by height or by the gap they cost; "paired above k, anything below". Test each with `hole_game` (cost = numbers left).
- **B10 Hole game beyond N = 24.** To see whether adjacent defects grow like N/6: a boolean "can D keep ≤ h broken pairs all game" table at 2 bits per position, layered and parallel, for N = 27, 28 (~2 GB).
- **B5 Endgames in Lean.** Formalize L7 (paper proof; statement shape in its section) via a membership form of `valueAux` (using L6); then three numbers left, cross-checked against Feng's case analysis (README, Known).

## A3

- **B4 Patch drawing strategies.** `strategy_eval` exists; leaderboard: fixed pick rules (Largest, Smallest, SmallestCatch, Exact, LeadOne, StayBehind) fail at N = 4 as player 1; rules that repair broken adjacent pairs hold N = 3, 4 as player 2 only. Patching fixed rules is aimless; a rule needs a region to steer into (A2) or the opponent's last pick (B9).

## A4

- **B3 Richer density notion.** Completeness nearly characterizes even-sum draws; find what its 523 exceptions with max ≤ 30 lack (`quad_step 30` lists the first). Complete sets fail badly at moderate gaps ({1,2,4,8,16} at gap 5 is a mover win), near-intervals don't (L4). Candidates: few holes relative to max (L4); consecutive numbers differ by ≤ 2; S ⊇ {1..k} with k ≥ max(S)/2.
