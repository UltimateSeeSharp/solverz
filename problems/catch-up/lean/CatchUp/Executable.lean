/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Executable.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; `value` comes from `CatchUp.Statement`;
module system.
-/
module

public import CatchUp.Classifier

/-!
# The verified evaluator

Claim C80 (`value_aux_add_scores`): adding the same amount to both scores leaves an ordinary-turn
position's value unchanged. `Position.eval` computes `Position.value` with two `check` calls
(`Position.eval_eq_value`), and `evalInitial` computes `value` (`eval_initial_eq_value`), so
`decide +kernel` proves concrete values.
-/

@[expose] public section

namespace CatchUp

open CatchUpSearch.CanAvoidLossClassifier

/-- Exact outcome of a normalized position, from the current player's perspective. -/
def Position.eval (position : Position) : Outcome :=
  let initial : GamePosition := ⟨position, .p1⟩
  if check .p1 initial then
    if check .p2 initial then .draw else .win
  else .loss

/-- Both safety queries together determine the full outcome. -/
theorem Position.eval_eq_value (position : Position) : position.eval = position.value := by
  have hp1 : check .p1 ⟨position, .p1⟩ = true ↔ position.value ≠ .loss := by
    simpa [can_avoid_loss_iff_value] using check_eq_true_iff .p1 ⟨position, .p1⟩
  have hp2 : check .p2 ⟨position, .p1⟩ = true ↔ position.value ≠ .win := by
    simpa [can_avoid_loss_iff_value] using check_eq_true_iff .p2 ⟨position, .p1⟩
  unfold Position.eval
  cases hvalue : position.value <;> simp_all

/-- Executable normalized evaluation agrees with the absolute-score specification. -/
theorem Position.eval_eq_value_aux (remaining : Finset ℕ) (s_me s_opp : ℕ)
    (hle : s_me ≤ s_opp) :
    Position.eval ⟨remaining, s_opp - s_me⟩ = valueAux remaining s_me s_opp false := by
  rw [Position.eval_eq_value, Position.value_eq_value_aux remaining s_me s_opp hle]

/-- Translating both scores leaves the ordinary-turn game unchanged. -/
theorem value_aux_add_scores (remaining : Finset ℕ) (s_me s_opp c : ℕ)
    (hle : s_me ≤ s_opp) :
    valueAux remaining (s_me + c) (s_opp + c) false =
      valueAux remaining s_me s_opp false := by
  rw [← Position.value_eq_value_aux remaining (s_me + c) (s_opp + c) (by omega),
    ← Position.value_eq_value_aux remaining s_me s_opp hle]
  rw [show s_opp + c - (s_me + c) = s_opp - s_me by omega]

/-- At tied zero scores, an ordinary pick and the forced single opening pick coincide. -/
theorem initial_position_value_eq (remaining : Finset ℕ) :
    Position.value ⟨remaining, 0⟩ = value remaining := by
  rw [show (0 : ℕ) = 0 - 0 from rfl, Position.value_eq_value_aux remaining 0 0 (by omega)]
  unfold value
  rw [valueAux.eq_def remaining 0 0 false, valueAux.eq_def remaining 0 0 true]
  simp

/-- Executable game value, including the empty game and the forced single-pick opening. -/
def evalInitial (remaining : Finset ℕ) : Outcome :=
  Position.eval ⟨remaining, 0⟩

/-- Initial executable evaluation computes exactly the literal reference game. -/
theorem eval_initial_eq_value (remaining : Finset ℕ) :
    evalInitial remaining = value remaining := by
  rw [evalInitial, Position.eval_eq_value, initial_position_value_eq]

/-- The conjecture includes the empty interval, which is already a draw. -/
theorem value_Icc_zero : value (Finset.Icc 1 0) = .draw := by
  simp [value, valueAux.eq_def]

end CatchUp
