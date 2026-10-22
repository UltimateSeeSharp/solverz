/-
Adapted from google-deepmind/formal-conjectures, FormalConjectures/Paper/CatchUpConjecture.lean
(commit 3b7c94e). Copyright 2025 The Formal Conjectures Authors, Apache License 2.0.
Changes: dropped the unused `Player` type and repository-specific attributes; the conjecture is a
`Prop` definition instead of a `sorry` theorem.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The Catch-Up game and conjecture

Catch-Up (Isaksen–Ismail–Brams–Nealen, 2015) is played on a finite set `S` of positive integers.
Each number a player removes is added to their score.

* Player 1 opens by removing exactly one number.
* Afterwards, the mover keeps removing numbers while strictly behind; the turn ends on the pick
  that brings their score to at least the opponent's.
* If even all remaining numbers would leave the mover behind, the mover loses.
* When `S` is empty, the higher score wins; equal scores are a draw.

`value S` is the outcome for player 1 under optimal play. `Conjecture` states that the game on
`{1, …, N}` is a draw whenever `1 + ⋯ + N` is even.
-/

@[expose] public section

namespace CatchUp

/-- The possible outcomes of a Catch-Up game. -/
inductive Outcome
  | win
  | loss
  | draw
deriving DecidableEq, Repr

/-- Negates an outcome, swapping win and loss. Used when switching player perspectives. -/
def Outcome.neg : Outcome → Outcome
  | win => loss
  | loss => win
  | draw => draw

/-- The best outcome for the current player from a list of possible outcomes:
win > draw > loss. -/
def Outcome.best (os : List Outcome) : Outcome :=
  os.foldl (fun
    | .win, _ => .win
    | _, .win => .win
    | .draw, _ => .draw
    | _, .draw => .draw
    | _, _ => .loss) .loss

/--
`valueAux remaining s_me s_opp isFirstMove` is the value, for the player about to act, of the
position with numbers `remaining` left, scores `s_me` (mover) and `s_opp` (opponent), assuming
optimal play. `isFirstMove` marks the opening, where exactly one number is taken.

A turn of several picks is modelled one pick at a time: while still strictly behind after a pick,
the same player moves again; once caught up, the opponent moves next.
-/
noncomputable def valueAux (remaining : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool) :
    Outcome :=
  if remaining = ∅ then
    if s_me > s_opp then .win
    else if s_opp > s_me then .loss
    else .draw
  else
    -- Even taking everything leaves the mover behind: they lose.
    if s_me + remaining.sum (fun x => x) < s_opp then
      .loss
    else
      let moves := remaining.attach.toList
      let outcomes := moves.map (fun ⟨x, _⟩ =>
        let s_me' := s_me + x
        let remaining' := remaining.erase x
        if isFirstMove then
          -- The opening is exactly one pick; then the turn passes.
          (valueAux remaining' s_opp s_me' false).neg
        else
          if s_me' ≥ s_opp then
            -- Caught up: the turn ends.
            (valueAux remaining' s_opp s_me' false).neg
          else
            -- Still strictly behind: same player picks again.
            valueAux remaining' s_me' s_opp false)
      .best outcomes
termination_by remaining.card
decreasing_by
  all_goals
    simpa [remaining'] using Finset.card_erase_lt_of_mem ‹_›

/-- The outcome for player 1 of Catch-Up on `S` under optimal play. -/
noncomputable def value (S : Finset ℕ) : Outcome :=
  valueAux S 0 0 true

/-- **Catch-Up conjecture.** If `1 + ⋯ + N = N (N + 1) / 2` is even, optimal play on
`{1, …, N}` ends in a draw. -/
def Conjecture : Prop :=
  ∀ N : ℕ, Even (N * (N + 1) / 2) → value (Finset.Icc 1 N) = .draw

end CatchUp
