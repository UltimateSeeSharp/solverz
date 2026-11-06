/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/LowerRayInteriorReduction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.DeficitWinningBound
public import CatchUp.BoCowgill.Earlier.LowerRayExactDeficit

/-!
# Interior reduction for the lower tied residuals

A winning interior opening of a tied consecutive-hole residual forces a loss at a dense
deficit-one child. Consequently, excluding those interior losses reduces every possible winning
opening to four explicit boundary candidates.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- If an available counter lacks one of its two neighbors in a tied consecutive-hole residual,
then it is one of four explicit boundary candidates. -/
theorem lower_ray_exact_deficit_residual_boundary_candidates
    (N b y : ℕ) (hy : y ∈ lowerRayExactDeficitResidual N b)
    (hboundary : y - 1 ∉ lowerRayExactDeficitResidual N b ∨
      y + 1 ∉ lowerRayExactDeficitResidual N b) :
    y = 2 ∨ y = b - 2 ∨ y = b + 1 ∨ y = N := by
  simp only [lowerRayExactDeficitResidual, Finset.mem_erase, Finset.mem_Icc] at hy hboundary
  omega

/-- Every interior left-neighbor deletion of a tied consecutive-hole residual is nonlosing at
deficit one. -/
def LowerRayInteriorDeficitOneNonloss (N b : ℕ) : Prop :=
  ∀ y, y ∈ lowerRayExactDeficitResidual N b →
    y - 1 ∈ lowerRayExactDeficitResidual N b →
    y + 1 ∈ lowerRayExactDeficitResidual N b →
    Position.value
      ⟨((lowerRayExactDeficitResidual N b).erase (y - 1)).erase y, 1⟩ ≠ .loss

/-- Once dense deficit-one losses are excluded, checking four boundary openings suffices to prove
that a tied consecutive-hole residual is nonwinning. -/
theorem lower_ray_exact_deficit_residual_value_ne_win_of_interior_and_boundary
    (N b : ℕ) (hN : 7 ≤ N) (hb : 3 ≤ b)
    (hinterior : LowerRayInteriorDeficitOneNonloss N b)
    (hboundary : ∀ y ∈ lowerRayExactDeficitResidual N b,
      (y = 2 ∨ y = b - 2 ∨ y = b + 1 ∨ y = N) →
        (afterOpening (lowerRayExactDeficitResidual N b) y).value ≠ .loss) :
    value (lowerRayExactDeficitResidual N b) ≠ .win := by
  intro hwin
  have hnonempty : (lowerRayExactDeficitResidual N b).Nonempty := by
    by_cases hbThree : b = 3
    · refine ⟨4, ?_⟩
      simp [lowerRayExactDeficitResidual, hbThree]
      omega
    · refine ⟨2, ?_⟩
      simp [lowerRayExactDeficitResidual]
      omega
  obtain ⟨y, hy, hyWin⟩ :=
    (value_eq_win_iff_exists_winning_opening
      (lowerRayExactDeficitResidual N b) hnonempty).mp hwin
  by_cases hyMinus : y - 1 ∈ lowerRayExactDeficitResidual N b
  · by_cases hyPlus : y + 1 ∈ lowerRayExactDeficitResidual N b
    · have hyPos : 0 < y := by
        simp only [lowerRayExactDeficitResidual, Finset.mem_erase, Finset.mem_Icc] at hy
        omega
      have hjump := after_opening_loss_forces_neighbor_value_jump
        (lowerRayExactDeficitResidual N b) y hyPos hyMinus hyPlus hyWin
      exact (hinterior y hy hyMinus hyPlus) hjump.1
    · exact hboundary y hy
        (lower_ray_exact_deficit_residual_boundary_candidates N b y hy (Or.inr hyPlus)) hyWin
  · exact hboundary y hy
      (lower_ray_exact_deficit_residual_boundary_candidates N b y hy (Or.inl hyMinus)) hyWin

/-- The first pair draw, dense interior nonloss, and the four boundary-opening checks imply the
interval draw theorem. -/
theorem value_Icc_eq_draw_of_lower_ray_interior_and_boundary
    (N : ℕ) (hN : 7 ≤ N)
    (hpairDraw : (pairDeletionPosition N 1 2).value = .draw)
    (hinterior : ∀ b, 3 ≤ b → b ≤ N → LowerRayInteriorDeficitOneNonloss N b)
    (hboundary : ∀ b, 3 ≤ b → b ≤ N →
      ∀ y ∈ lowerRayExactDeficitResidual N b,
        (y = 2 ∨ y = b - 2 ∨ y = b + 1 ∨ y = N) →
          (afterOpening (lowerRayExactDeficitResidual N b) y).value ≠ .loss) :
    value (Finset.Icc 1 N) = .draw := by
  apply value_Icc_eq_draw_of_lower_pair_deletion_nonloss N (by omega)
  · apply lower_pair_deletion_nonloss_of_exact_deficit_residuals N
    · rw [hpairDraw]
      simp
    · intro b hb hbN
      exact lower_ray_exact_deficit_residual_value_ne_win_of_interior_and_boundary
        N b hN hb (hinterior b hb hbN) (hboundary b hb hbN)
  · exact hpairDraw

end CatchUp
