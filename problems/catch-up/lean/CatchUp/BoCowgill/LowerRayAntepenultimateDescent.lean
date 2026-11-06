/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/LowerRayAntepenultimateDescent.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.DeficitWinningBound
public import CatchUp.BoCowgill.DrawOpening

/-!
# Antepenultimate lower-ray descent

A draw after opening one in the interval of size `N - 4` implies nonloss at
`pairDeletionPosition N 1 (N - 2)`. The available-deficit obstruction leaves only
the two largest counters as possible winning residual openings. Replying with
the other one returns to the smaller drawn position.

The argument uses the winning-opening bound from `CatchUp.Earlier.DeficitWinningBound`
and the opening-order identity from `CatchUp.DrawOpening`.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

private theorem value_ne_loss_of_draw_move
    (position : Position) (x : ℕ) (hx : x ∈ position.remaining)
    (hmove : position.moveOutcome x = .draw) : position.value ≠ .loss := by
  have hcatch : ¬ position.remaining.sum (fun y ↦ y) < position.deficit := by
    intro hsum
    have hloss := position.move_outcome_eq_loss_of_sum_lt_deficit hx hsum
    simp [hmove] at hloss
  rw [Position.value_eq_best_move_outcome position (Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩) hcatch,
    Outcome.best_ne_loss_iff]
  refine ⟨position.moveOutcome x, List.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩, ?_⟩
  simp [hmove]

/-- Drawing opening one four sizes below prevents loss at the antepenultimate lower-ray state. -/
theorem pair_deletion_position_antepenultimate_value_ne_loss_of_opening_one_draw
    (N : ℕ) (hN : 7 ≤ N)
    (hdraw : (afterOpening (Finset.Icc 1 (N - 4)) 1).value = .draw) :
    (pairDeletionPosition N 1 (N - 2)).value ≠ .loss := by
  intro hloss
  let remaining := ((Finset.Icc 1 N).erase 1).erase (N - 2)
  have hdeficit : N - 3 ∈ remaining := by
    simp [remaining]
    omega
  obtain ⟨_, y, hyResidual, hyLoss, hyLarger, _⟩ :=
    loss_with_available_deficit_forces_large_unique_winning_opening
      remaining (N - 3) hdeficit (by
        simpa [remaining, pairDeletionPosition, Nat.sub_sub] using hloss)
  have hyCases : y = N - 1 ∨ y = N := by
    simp only [remaining, Finset.mem_erase, Finset.mem_Icc] at hyResidual
    omega
  let residual := remaining.erase (N - 3)
  have hafter : (afterOpening residual (N - 1)).afterPick N =
      afterOpening (Finset.Icc 1 (N - 4)) 1 := by
    simp only [afterOpening, Position.afterPick]
    congr 1
    · ext x
      simp [residual, remaining]
      omega
    · show (if N < N - 1 then N - 1 - N else N - (N - 1)) = 1
      split <;> omega
  have hmove : (afterOpening residual (N - 1)).moveOutcome N = .draw := by
    rw [Position.moveOutcome, hafter, hdraw]
    simp [Outcome.neg]
  rcases hyCases with hyEq | hyEq
  · subst y
    apply value_ne_loss_of_draw_move (afterOpening residual (N - 1)) N ?_ hmove hyLoss
    simp [afterOpening, residual, remaining]
    omega
  · subst y
    have hmove' : (afterOpening residual N).moveOutcome (N - 1) = .draw := by
      rw [move_outcome_after_opening_comm residual (show N ≠ N - 1 by omega), hmove]
      rfl
    apply value_ne_loss_of_draw_move (afterOpening residual N) (N - 1) ?_ hmove' hyLoss
    simp [afterOpening, residual, remaining]
    omega

end CatchUp
