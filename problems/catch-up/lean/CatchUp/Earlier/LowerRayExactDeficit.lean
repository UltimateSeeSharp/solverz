/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/LowerRayExactDeficit.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.DrawOpening
public import CatchUp.PairDeletion

/-!
# Exact-deficit reduction for the lower pair-deletion ray

For every lower pair-deletion state except the first one, the counter equal to the deficit remains
available. Taking it reaches a tied interval with two consecutive holes. This module packages that
identity and reduces the interval draw conjecture to nonwinning, or drawing, tied residual roots.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- The tied residual obtained by deleting the exact deficit from a lower pair-deletion state. -/
def lowerRayExactDeficitResidual (N b : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 N).erase (b - 1)).erase b

/-- The normalized position after opening a generic tied residual at `2`. -/
def lowerRayExactDeficitOpeningTwoPosition (N b : ℕ) : Position :=
  ⟨((Finset.Icc 3 N).erase (b - 1)).erase b, 2⟩

/-- The normalized position after opening the `b = 3` tied residual at `4`. -/
def lowerRayExactDeficitOpeningFourPosition (N : ℕ) : Position :=
  ⟨Finset.Icc 5 N, 4⟩

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

/-- The exact deficit remains available on every lower-ray state with `b ≥ 3`. -/
theorem pred_mem_pair_deletion_position
    (N b : ℕ) (hb : 3 ≤ b) (hbN : b ≤ N) :
    b - 1 ∈ (pairDeletionPosition N 1 b).remaining := by
  simp [pairDeletionPosition]
  omega

/-- Taking the exact deficit reaches the tied consecutive-hole residual. -/
theorem pair_deletion_position_after_pick_pred
    (N b : ℕ) (hb : 3 ≤ b) :
    (pairDeletionPosition N 1 b).afterPick (b - 1) =
      ⟨lowerRayExactDeficitResidual N b, 0⟩ := by
  simp only [pairDeletionPosition, lowerRayExactDeficitResidual, Position.afterPick]
  have hnotlt : ¬b - 1 < b - 1 := by omega
  simp only [hnotlt, ite_false]
  congr 1
  · ext x
    simp
    omega
  · omega

/-- The exact-deficit move is the negated value of the tied consecutive-hole residual. -/
theorem pair_deletion_position_move_outcome_pred
    (N b : ℕ) (hb : 3 ≤ b) :
    (pairDeletionPosition N 1 b).moveOutcome (b - 1) =
      (value (lowerRayExactDeficitResidual N b)).neg := by
  rw [Position.moveOutcome]
  have hnotlt : ¬b - 1 < (pairDeletionPosition N 1 b).deficit := by
    simp [pairDeletionPosition]
  simp only [hnotlt, ite_false]
  rw [pair_deletion_position_after_pick_pred N b hb,
    position_value_zero_deficit_eq_value]

/-- A nonwinning tied residual makes the corresponding lower pair-deletion state nonlosing. -/
theorem pair_deletion_position_value_ne_loss_of_exact_deficit_residual_ne_win
    (N b : ℕ) (hb : 3 ≤ b) (hbN : b ≤ N)
    (hresidual : value (lowerRayExactDeficitResidual N b) ≠ .win) :
    (pairDeletionPosition N 1 b).value ≠ .loss := by
  let position := pairDeletionPosition N 1 b
  have hpred : b - 1 ∈ position.remaining := by
    simpa [position] using pred_mem_pair_deletion_position N b hb hbN
  have hremaining : position.remaining ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨b - 1, hpred⟩
  have hsum : b - 1 ≤ position.remaining.sum (fun x ↦ x) :=
    Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hpred
  have hcatch : ¬position.remaining.sum (fun x ↦ x) < position.deficit := by
    change ¬position.remaining.sum (fun x ↦ x) < b - 1
    omega
  rw [Position.value_eq_best_move_outcome position hremaining hcatch,
    Outcome.best_ne_loss_iff]
  refine ⟨position.moveOutcome (b - 1), ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨⟨b - 1, hpred⟩, by simp, rfl⟩
  · rw [show position.moveOutcome (b - 1) =
        (value (lowerRayExactDeficitResidual N b)).neg by
      simpa [position] using pair_deletion_position_move_outcome_pred N b hb]
    exact (Outcome.neg_ne_loss_iff _).mpr hresidual

/-- Opening a generic tied residual at `2` gives the named constant-deficit position. -/
theorem lower_ray_exact_deficit_residual_after_opening_two
    (N b : ℕ) (hb : 4 ≤ b) :
    afterOpening (lowerRayExactDeficitResidual N b) 2 =
      lowerRayExactDeficitOpeningTwoPosition N b := by
  simp only [afterOpening, lowerRayExactDeficitResidual,
    lowerRayExactDeficitOpeningTwoPosition]
  congr 1
  ext x
  simp
  omega

/-- Opening the `b = 3` tied residual at `4` leaves the interval beginning at `5`. -/
theorem lower_ray_exact_deficit_residual_three_after_opening_four (N : ℕ) :
    afterOpening (lowerRayExactDeficitResidual N 3) 4 =
      lowerRayExactDeficitOpeningFourPosition N := by
  simp only [afterOpening, lowerRayExactDeficitResidual,
    lowerRayExactDeficitOpeningFourPosition]
  congr 1
  ext x
  simp
  omega

/-- Nonloss at `b = 2` and nonwinning tied residuals thereafter imply the lower ray. -/
theorem lower_pair_deletion_nonloss_of_exact_deficit_residuals
    (N : ℕ)
    (hpairTwo : (pairDeletionPosition N 1 2).value ≠ .loss)
    (hresidual : ∀ b, 3 ≤ b → b ≤ N →
      value (lowerRayExactDeficitResidual N b) ≠ .win) :
    LowerPairDeletionNonloss N := by
  intro b hbIcc hbOne
  have hbN : b ≤ N := (Finset.mem_Icc.mp hbIcc).2
  by_cases hbTwo : b = 2
  · subst b
    exact hpairTwo
  have hbThree : 3 ≤ b := by omega
  exact pair_deletion_position_value_ne_loss_of_exact_deficit_residual_ne_win
    N b hbThree hbN (hresidual b hbThree hbN)

/-- Drawing tied residuals and the first draw pair imply that the interval game is a draw. -/
theorem value_Icc_eq_draw_of_exact_deficit_residual_draws
    (N : ℕ) (hN : 2 ≤ N)
    (hpairDraw : (pairDeletionPosition N 1 2).value = .draw)
    (hresidual : ∀ b, 3 ≤ b → b ≤ N →
      value (lowerRayExactDeficitResidual N b) = .draw) :
    value (Finset.Icc 1 N) = .draw := by
  apply value_Icc_eq_draw_of_lower_pair_deletion_nonloss N hN
  · apply lower_pair_deletion_nonloss_of_exact_deficit_residuals N
    · rw [hpairDraw]
      simp
    · intro b hb hbN
      rw [hresidual b hb hbN]
      simp
  · exact hpairDraw

/-- A drawing opening in every tied residual suffices for the interval draw theorem. -/
theorem value_Icc_eq_draw_of_exact_deficit_residual_draw_openings
    (N : ℕ) (hN : 2 ≤ N)
    (hpairDraw : (pairDeletionPosition N 1 2).value = .draw)
    (hopenings : ∀ b, 3 ≤ b → b ≤ N →
      ∃ p ∈ lowerRayExactDeficitResidual N b,
        (afterOpening (lowerRayExactDeficitResidual N b) p).value = .draw) :
    value (Finset.Icc 1 N) = .draw := by
  apply value_Icc_eq_draw_of_exact_deficit_residual_draws N hN hpairDraw
  intro b hb hbN
  obtain ⟨p, hp, hpdraw⟩ := hopenings b hb hbN
  apply (value_eq_draw_iff_exists_draw_after_opening
    (lowerRayExactDeficitResidual N b) ⟨p, hp⟩).2
  exact ⟨p, hp, hpdraw⟩

/-- It suffices to draw the canonical opening `4` at the first residual and opening `2` at every
later residual. -/
theorem value_Icc_eq_draw_of_exact_deficit_canonical_openings
    (N : ℕ) (hN : 4 ≤ N)
    (hpairDraw : (pairDeletionPosition N 1 2).value = .draw)
    (hthree : (lowerRayExactDeficitOpeningFourPosition N).value = .draw)
    (hlater : ∀ b, 4 ≤ b → b ≤ N →
      (lowerRayExactDeficitOpeningTwoPosition N b).value = .draw) :
    value (Finset.Icc 1 N) = .draw := by
  apply value_Icc_eq_draw_of_exact_deficit_residual_draw_openings N (by omega) hpairDraw
  intro b hb hbN
  by_cases hbThree : b = 3
  · subst b
    refine ⟨4, ?_, ?_⟩
    · simp [lowerRayExactDeficitResidual]
      omega
    · rw [lower_ray_exact_deficit_residual_three_after_opening_four]
      exact hthree
  · have hbFour : 4 ≤ b := by omega
    refine ⟨2, ?_, ?_⟩
    · simp [lowerRayExactDeficitResidual]
      omega
    · rw [lower_ray_exact_deficit_residual_after_opening_two N b hbFour]
      exact hlater b hbFour hbN

end CatchUp
