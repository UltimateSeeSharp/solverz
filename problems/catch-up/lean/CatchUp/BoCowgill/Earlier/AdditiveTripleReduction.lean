/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/AdditiveTripleReduction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.LowerRayExactDeficit
public import CatchUp.BoCowgill.Earlier.ReplyDigraphReduction

/-!
# Additive-triple residuals for Catch-Up pair states

For openings `a < b`, the pair-deletion deficit is `b - a`. Except when `b = 2a`, that counter
is still available, so taking it catches exactly and removes the additive triple
`{a, b - a, b}`. In the nontrivial doubling case `b = 2a` with `a > 1`, there is instead a
canonical catch at `a + 1`; the first pair `(1, 2)` is supplied separately as the neutral witness.
This module reduces nonloss of every pair state, and hence the interval draw, to nonwinning
residuals of these two forms. It makes no claim that the residual hypotheses hold.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- The tied residual obtained by deleting `a`, `b`, and their difference from the interval. -/
def additiveTripleResidual (N a b : ℕ) : Finset ℕ :=
  (((Finset.Icc 1 N).erase a).erase b).erase (b - a)

/-- The one-deficit child obtained in the doubling case `b = 2a`, for `a > 1`. -/
def doublingPairResidualPosition (N a : ℕ) : Position :=
  ⟨(((Finset.Icc 1 N).erase a).erase (2 * a)).erase (a + 1), 1⟩

private theorem Position.value_ne_loss_of_legal_move
    (position : Position) (x : ℕ)
    (hx : x ∈ position.remaining)
    (hxcatch : position.deficit ≤ x)
    (hmove : position.moveOutcome x ≠ .loss) :
    position.value ≠ .loss := by
  have hremaining : position.remaining ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩
  have hxle : x ≤ position.remaining.sum (fun y ↦ y) :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  have hcatch : ¬position.remaining.sum (fun y ↦ y) < position.deficit := by
    omega
  rw [Position.value_eq_best_move_outcome position hremaining hcatch,
    Outcome.best_ne_loss_iff]
  refine ⟨position.moveOutcome x, ?_, hmove⟩
  apply List.mem_map.mpr
  exact ⟨⟨x, hx⟩, by simp, rfl⟩

/-- Picking the exact opening difference reaches the tied additive-triple residual. -/
theorem pair_deletion_position_after_pick_difference (N a b : ℕ) :
    (pairDeletionPosition N a b).afterPick (b - a) =
      ⟨additiveTripleResidual N a b, 0⟩ := by
  simp [pairDeletionPosition, additiveTripleResidual, Position.afterPick]

/-- The exact-difference move has the negated value of the tied additive-triple residual. -/
theorem pair_deletion_position_move_outcome_difference (N a b : ℕ) :
    (pairDeletionPosition N a b).moveOutcome (b - a) =
      (value (additiveTripleResidual N a b)).neg := by
  rw [Position.moveOutcome]
  have hnotlt : ¬b - a < (pairDeletionPosition N a b).deficit := by
    simp [pairDeletionPosition]
  simp only [hnotlt, ite_false]
  rw [pair_deletion_position_after_pick_difference,
    position_value_zero_deficit_eq_value]

/-- If the difference is still available and the tied residual is nonwinning, the original pair
state is nonlosing. -/
theorem pair_deletion_position_value_ne_loss_of_additive_residual_ne_win
    (N a b : ℕ)
    (hdifference : b - a ∈ (pairDeletionPosition N a b).remaining)
    (hresidual : value (additiveTripleResidual N a b) ≠ .win) :
    (pairDeletionPosition N a b).value ≠ .loss := by
  apply Position.value_ne_loss_of_legal_move _ (b - a) hdifference
  · simp [pairDeletionPosition]
  rw [pair_deletion_position_move_outcome_difference]
  exact (Outcome.neg_ne_loss_iff _).mpr hresidual

/-- Away from the doubling case `b = 2a`, the opening difference remains in the interval pair
state. -/
theorem difference_mem_pair_deletion_position
    (N a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hbN : b ≤ N)
    (hdouble : b ≠ 2 * a) :
    b - a ∈ (pairDeletionPosition N a b).remaining := by
  simp [pairDeletionPosition]
  omega

/-- Nonwinning additive-triple residuals make all nondoubling interval pair states nonlosing. -/
theorem pair_deletion_position_value_ne_loss_of_additive_residual_ne_win_of_not_double
    (N a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hbN : b ≤ N)
    (hdouble : b ≠ 2 * a)
    (hresidual : value (additiveTripleResidual N a b) ≠ .win) :
    (pairDeletionPosition N a b).value ≠ .loss := by
  apply pair_deletion_position_value_ne_loss_of_additive_residual_ne_win N a b
  · exact difference_mem_pair_deletion_position N a b ha hab hbN hdouble
  · exact hresidual

/-- In a nontrivial doubling pair, counter `a+1` catches and reaches the named one-deficit
residual. -/
theorem doubling_pair_deletion_position_after_pick_succ (N a : ℕ) :
    (pairDeletionPosition N a (2 * a)).afterPick (a + 1) =
      doublingPairResidualPosition N a := by
  simp [pairDeletionPosition, doublingPairResidualPosition, Position.afterPick, two_mul]

/-- The `a+1` move in a doubling pair has the negated value of its one-deficit residual. -/
theorem doubling_pair_deletion_position_move_outcome_succ (N a : ℕ) :
    (pairDeletionPosition N a (2 * a)).moveOutcome (a + 1) =
      (doublingPairResidualPosition N a).value.neg := by
  rw [Position.moveOutcome]
  have hnotlt : ¬a + 1 < (pairDeletionPosition N a (2 * a)).deficit := by
    simp [pairDeletionPosition, two_mul]
  simp only [hnotlt, ite_false]
  rw [doubling_pair_deletion_position_after_pick_succ]

/-- Counter `a+1` is available in every nontrivial interval doubling pair. -/
theorem succ_mem_doubling_pair_deletion_position
    (N a : ℕ) (ha : 2 ≤ a) (hdoubleN : 2 * a ≤ N) :
    a + 1 ∈ (pairDeletionPosition N a (2 * a)).remaining := by
  simp [pairDeletionPosition, two_mul]
  omega

/-- A nonwinning one-deficit residual makes the corresponding doubling pair nonlosing. -/
theorem doubling_pair_deletion_position_value_ne_loss_of_residual_ne_win
    (N a : ℕ) (ha : 2 ≤ a) (hdoubleN : 2 * a ≤ N)
    (hresidual : (doublingPairResidualPosition N a).value ≠ .win) :
    (pairDeletionPosition N a (2 * a)).value ≠ .loss := by
  apply Position.value_ne_loss_of_legal_move _ (a + 1)
  · exact succ_mem_doubling_pair_deletion_position N a ha hdoubleN
  · simp [pairDeletionPosition, two_mul]
  · rw [doubling_pair_deletion_position_move_outcome_succ]
    exact (Outcome.neg_ne_loss_iff _).mpr hresidual

/-- Additive-triple residual nonwins, doubling-residual nonwins, and the first pair imply nonloss
of every above-diagonal pair-deletion state. -/
theorem all_pair_deletion_nonloss_of_additive_residuals
    (N : ℕ)
    (hpairTwo : (pairDeletionPosition N 1 2).value ≠ .loss)
    (hadditive : ∀ a b, 1 ≤ a → a < b → b ≤ N → b ≠ 2 * a →
      value (additiveTripleResidual N a b) ≠ .win)
    (hdouble : ∀ a, 2 ≤ a → 2 * a ≤ N →
      (doublingPairResidualPosition N a).value ≠ .win) :
    ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N, a < b →
      (pairDeletionPosition N a b).value ≠ .loss := by
  intro a ha b hb hab
  have haOne : 1 ≤ a := (Finset.mem_Icc.mp ha).1
  have hbN : b ≤ N := (Finset.mem_Icc.mp hb).2
  by_cases hdoubleEq : b = 2 * a
  · by_cases haEq : a = 1
    · subst a
      have hbEq : b = 2 := by simpa using hdoubleEq
      subst b
      exact hpairTwo
    · have haTwo : 2 ≤ a := by omega
      subst b
      exact doubling_pair_deletion_position_value_ne_loss_of_residual_ne_win
        N a haTwo hbN (hdouble a haTwo hbN)
  · exact pair_deletion_position_value_ne_loss_of_additive_residual_ne_win_of_not_double
      N a b haOne hab hbN hdoubleEq (hadditive a b haOne hab hbN hdoubleEq)

/-- The additive-triple and doubling residual families reduce the interval draw to the already
isolated neutral first pair. -/
theorem value_Icc_eq_draw_of_additive_residuals
    (N : ℕ) (hN : 3 ≤ N)
    (hpairDraw : (pairDeletionPosition N 1 2).value = .draw)
    (hadditive : ∀ a b, 1 ≤ a → a < b → b ≤ N → b ≠ 2 * a →
      value (additiveTripleResidual N a b) ≠ .win)
    (hdouble : ∀ a, 2 ≤ a → 2 * a ≤ N →
      (doublingPairResidualPosition N a).value ≠ .win) :
    value (Finset.Icc 1 N) = .draw := by
  apply value_Icc_eq_draw_of_all_pair_deletion_nonloss_and_neutral_at_one N hN
  · apply all_pair_deletion_nonloss_of_additive_residuals N
    · rw [hpairDraw]
      simp
    · exact hadditive
    · exact hdouble
  · refine ⟨2, ?_⟩
    refine ⟨by simp; omega, by simp; omega, by omega, ?_⟩
    have hafter :
        (afterOpening (Finset.Icc 1 N) 1).afterPick 2 =
          pairDeletionPosition N 1 2 := by
      simp [afterOpening, Position.afterPick, pairDeletionPosition]
    rw [Position.moveOutcome]
    have hnotlt : ¬2 < (afterOpening (Finset.Icc 1 N) 1).deficit := by
      simp [afterOpening]
    simp only [hnotlt, ite_false]
    rw [hafter, hpairDraw]
    rfl

end CatchUp
