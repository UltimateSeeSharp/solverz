/-
Under catch-up-research's Apache License, Version 2.0 (no notice in the file); see
https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ZeroDeficit.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.Executable

/-!
# ZeroDeficit

Connects normalized tied-score positions to the initial game value.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp
/-- A zero-deficit normalized position has the same value as the corresponding Catch-Up root. -/
theorem position_value_zero_deficit_eq_value (S : Finset ℕ) :
    Position.value ⟨S, 0⟩ = value S := by
  rw [Position.value_eq_value_aux S 0 0 (by omega)]
  rw [value]
  rw [valueAux.eq_def, valueAux.eq_def]
  by_cases hS : S = ∅
  · simp [hS]
  · simp only [hS, Nat.zero_add, Nat.not_lt_zero, ite_false]
    congr 1

end CatchUp
