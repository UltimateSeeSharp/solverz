/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/LowerRayFifthEndpoint.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.ExactSumResiduals
public import CatchUp.Earlier.DeficitWinningBound

/-!
# Exact-sum exchanges for a four-counter upper tail

The exact-sum obstruction excludes every upper opening in
$[2,m] \cup \{m+3,m+4,m+5,m+6\}$ for $m \ge 17$.
Consequently the fifth-from-top lower-ray position is nonlosing for $N \ge 23$.
The proof uses the exact-sum residual-exclusion interface and the verified lower-ray
winning-opening bound. It does not assume parity, a smaller-instance draw, or the
Catch-Up conjecture.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

set_option maxHeartbeats 2000000
namespace CatchUp

/-- The lower interval with a two-counter gap and four consecutive upper counters. -/
def upperQuadrupleResidual (m : ℕ) : Finset ℕ :=
  Finset.Icc 2 m ∪ {m + 3, m + 4, m + 5, m + 6}

/-- Exclusion of upper opening 3 in the four-counter tail. -/
theorem upper_quadruple_first_opening_ne_loss (m : ℕ) (hm : 17 ≤ m) :
    (afterOpening (upperQuadrupleResidual m) (m + 3)).value ≠ .loss := by
  apply Position.value_ne_loss_of_exact_sum_residuals _ {3, m} _ m
  · simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp [upperQuadrupleResidual]
    omega
  · simp [show 3 ≠ m by omega]
    omega
  · intro w hw hgt
    have hcases : w = (m + 4) ∨ w = (m + 5) ∨ w = (m + 6) := by
      simp [upperQuadrupleResidual] at hw
      omega
    rcases hcases with rfl | rfl | rfl
    · apply Position.value_ne_loss_of_exact_sum_residuals _ {5, (m - 1)} _ (m - 1)
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [upperQuadrupleResidual]
        omega
      · simp [show 5 ≠ (m - 1) by omega]
        omega
      · intro w hw hgt
        have hcases : w = (m + 5) ∨ w = (m + 6) := by
          simp [upperQuadrupleResidual] at hw
          omega
        rcases hcases with rfl | rfl
        · apply Position.value_ne_loss_of_exact_sum_residuals _ {7, (m - 2)} _ (m - 2)
          · simp
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            omega
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp [upperQuadrupleResidual]
            omega
          · simp [show 7 ≠ (m - 2) by omega]
            omega
          · intro w hw hgt
            have hcases : w = (m + 6) := by
              simp [upperQuadrupleResidual] at hw
              omega
            subst w
            apply Position.value_ne_loss_of_exact_sum_residuals _ {9, (m - 3)} _ (m - 3)
            · simp
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              omega
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp [upperQuadrupleResidual]
              omega
            · simp [show 9 ≠ (m - 3) by omega]
              omega
            · intro w hw hgt
              simp [upperQuadrupleResidual] at hw
              omega
        · apply Position.value_ne_loss_of_exact_sum_residuals _ {8, (m - 2)} _ (m - 2)
          · simp
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            omega
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp [upperQuadrupleResidual]
            omega
          · simp [show 8 ≠ (m - 2) by omega]
            omega
          · intro w hw hgt
            have hcases : w = (m + 5) := by
              simp [upperQuadrupleResidual] at hw
              omega
            subst w
            apply Position.value_ne_loss_of_exact_sum_residuals _ {2, 6, (m - 3)} _ (m - 3)
            · simp
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              omega
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp [upperQuadrupleResidual]
              omega
            · simp [show 2 ≠ 6 by omega, show 2 ≠ (m - 3) by omega, show 6 ≠ (m - 3) by omega]
              omega
            · intro w hw hgt
              simp [upperQuadrupleResidual] at hw
              omega
    · apply Position.value_ne_loss_of_exact_sum_residuals _ {6, (m - 1)} _ (m - 1)
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [upperQuadrupleResidual]
        omega
      · simp [show 6 ≠ (m - 1) by omega]
        omega
      · intro w hw hgt
        have hcases : w = (m + 4) ∨ w = (m + 6) := by
          simp [upperQuadrupleResidual] at hw
          omega
        rcases hcases with rfl | rfl
        · apply Position.value_ne_loss_of_exact_sum_residuals _ {2, 4, (m - 2)} _ (m - 2)
          · simp
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            omega
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp [upperQuadrupleResidual]
            omega
          · simp [show 2 ≠ 4 by omega, show 2 ≠ (m - 2) by omega, show 4 ≠ (m - 2) by omega]
            omega
          · intro w hw hgt
            have hcases : w = (m + 6) := by
              simp [upperQuadrupleResidual] at hw
              omega
            subst w
            apply Position.value_ne_loss_of_exact_sum_residuals _ {9, (m - 3)} _ (m - 3)
            · simp
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              omega
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp [upperQuadrupleResidual]
              omega
            · simp [show 9 ≠ (m - 3) by omega]
              omega
            · intro w hw hgt
              simp [upperQuadrupleResidual] at hw
              omega
        · apply Position.value_ne_loss_of_exact_sum_residuals _ {2, (m + 4)} _ (m + 4)
          · simp
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            omega
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp [upperQuadrupleResidual]
            omega
          · simp
            omega
          · intro w hw hgt
            simp [upperQuadrupleResidual] at hw
            omega
    · apply Position.value_ne_loss_of_exact_sum_residuals _ {2, (m + 4)} _ (m + 4)
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [upperQuadrupleResidual]
        omega
      · simp
        omega
      · intro w hw hgt
        have hcases : w = (m + 5) := by
          simp [upperQuadrupleResidual] at hw
          omega
        subst w
        apply Position.value_ne_loss_of_exact_sum_residuals _ {6, (m - 1)} _ (m - 1)
        · simp
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          omega
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp [upperQuadrupleResidual]
          omega
        · simp [show 6 ≠ (m - 1) by omega]
          omega
        · intro w hw hgt
          simp [upperQuadrupleResidual] at hw
          omega

/-- Exclusion of upper opening 4 in the four-counter tail. -/
theorem upper_quadruple_second_opening_ne_loss (m : ℕ) (hm : 17 ≤ m) :
    (afterOpening (upperQuadrupleResidual m) (m + 4)).value ≠ .loss := by
  apply Position.value_ne_loss_of_exact_sum_residuals _ {4, m} _ m
  · simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp [upperQuadrupleResidual]
    omega
  · simp [show 4 ≠ m by omega]
    omega
  · intro w hw hgt
    have hcases : w = (m + 3) ∨ w = (m + 5) ∨ w = (m + 6) := by
      simp [upperQuadrupleResidual] at hw
      omega
    rcases hcases with rfl | rfl | rfl
    · apply Position.value_ne_loss_of_exact_sum_residuals _ {5, (m - 2)} _ (m - 2)
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [upperQuadrupleResidual]
        omega
      · simp [show 5 ≠ (m - 2) by omega]
        omega
      · intro w hw hgt
        have hcases : w = (m - 1) ∨ w = (m + 5) ∨ w = (m + 6) := by
          simp [upperQuadrupleResidual] at hw
          omega
        rcases hcases with rfl | rfl | rfl
        · apply Position.value_ne_loss_of_exact_sum_residuals _ {2, (m - 3)} _ (m - 3)
          · simp
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            omega
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp [upperQuadrupleResidual]
            omega
          · simp [show 2 ≠ (m - 3) by omega]
            omega
          · intro w hw hgt
            have hcases : w = (m + 5) ∨ w = (m + 6) := by
              simp [upperQuadrupleResidual] at hw
              omega
            rcases hcases with rfl | rfl
            · apply Position.value_ne_loss_of_exact_sum_residuals _ {9, (m - 4)} _ (m - 4)
              · simp
              · intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                omega
              · intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                simp [upperQuadrupleResidual]
                omega
              · simp [show 9 ≠ (m - 4) by omega]
                omega
              · intro w hw hgt
                have hcases : w = (m + 6) := by
                  simp [upperQuadrupleResidual] at hw
                  omega
                subst w
                apply Position.value_ne_loss_of_exact_sum_residuals _ {11, (m - 5)} _ (m - 5)
                · simp
                · intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  omega
                · intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  simp [upperQuadrupleResidual]
                  omega
                · simp [show 11 ≠ (m - 5) by omega]
                  omega
                · intro w hw hgt
                  simp [upperQuadrupleResidual] at hw
                  omega
            · apply Position.value_ne_loss_of_exact_sum_residuals _ {10, (m - 4)} _ (m - 4)
              · simp
              · intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                omega
              · intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                simp [upperQuadrupleResidual]
                omega
              · simp [show 10 ≠ (m - 4) by omega]
                omega
              · intro w hw hgt
                have hcases : w = (m + 5) := by
                  simp [upperQuadrupleResidual] at hw
                  omega
                subst w
                apply Position.value_ne_loss_of_exact_sum_residuals _ {3, 7, (m - 5)} _ (m - 5)
                · simp
                · intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  omega
                · intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  simp [upperQuadrupleResidual]
                  omega
                · simp [show 3 ≠ 7 by omega, show 3 ≠ (m - 5) by omega, show 7 ≠ (m - 5) by omega]
                  omega
                · intro w hw hgt
                  simp [upperQuadrupleResidual] at hw
                  omega
        · apply Position.value_ne_loss_of_exact_sum_residuals _ {6, (m - 1)} _ (m - 1)
          · simp
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            omega
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp [upperQuadrupleResidual]
            omega
          · simp [show 6 ≠ (m - 1) by omega]
            omega
          · intro w hw hgt
            have hcases : w = (m + 6) := by
              simp [upperQuadrupleResidual] at hw
              omega
            subst w
            apply Position.value_ne_loss_of_exact_sum_residuals _ {9, (m - 3)} _ (m - 3)
            · simp
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              omega
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp [upperQuadrupleResidual]
              omega
            · simp [show 9 ≠ (m - 3) by omega]
              omega
            · intro w hw hgt
              simp [upperQuadrupleResidual] at hw
              omega
        · apply Position.value_ne_loss_of_exact_sum_residuals _ {7, (m - 1)} _ (m - 1)
          · simp
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            omega
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp [upperQuadrupleResidual]
            omega
          · simp [show 7 ≠ (m - 1) by omega]
            omega
          · intro w hw hgt
            have hcases : w = (m + 5) := by
              simp [upperQuadrupleResidual] at hw
              omega
            subst w
            apply Position.value_ne_loss_of_exact_sum_residuals _ {8, (m - 3)} _ (m - 3)
            · simp
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              omega
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp [upperQuadrupleResidual]
              omega
            · simp [show 8 ≠ (m - 3) by omega]
              omega
            · intro w hw hgt
              simp [upperQuadrupleResidual] at hw
              omega
    · apply Position.value_ne_loss_of_exact_sum_residuals _ {2, (m + 3)} _ (m + 3)
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [upperQuadrupleResidual]
        omega
      · simp
        omega
      · intro w hw hgt
        have hcases : w = (m + 6) := by
          simp [upperQuadrupleResidual] at hw
          omega
        subst w
        apply Position.value_ne_loss_of_exact_sum_residuals _ {7, (m - 1)} _ (m - 1)
        · simp
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          omega
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp [upperQuadrupleResidual]
          omega
        · simp [show 7 ≠ (m - 1) by omega]
          omega
        · intro w hw hgt
          simp [upperQuadrupleResidual] at hw
          omega
    · apply Position.value_ne_loss_of_exact_sum_residuals _ {3, (m + 3)} _ (m + 3)
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [upperQuadrupleResidual]
        omega
      · simp only [Finset.sum_pair (by omega : 3 ≠ m + 3)]
        omega
      · intro w hw hgt
        have hcases : w = (m + 5) := by
          simp [upperQuadrupleResidual] at hw
          omega
        subst w
        apply Position.value_ne_loss_of_exact_sum_residuals _ {6, (m - 1)} _ (m - 1)
        · simp
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          omega
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp [upperQuadrupleResidual]
          omega
        · simp [show 6 ≠ (m - 1) by omega]
          omega
        · intro w hw hgt
          simp [upperQuadrupleResidual] at hw
          omega

/-- Exclusion of upper opening 5 in the four-counter tail. -/
theorem upper_quadruple_third_opening_ne_loss (m : ℕ) (hm : 17 ≤ m) :
    (afterOpening (upperQuadrupleResidual m) (m + 5)).value ≠ .loss := by
  apply Position.value_ne_loss_of_exact_sum_residuals _ {2, (m + 3)} _ (m + 3)
  · simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp [upperQuadrupleResidual]
    omega
  · simp
    omega
  · intro w hw hgt
    have hcases : w = (m + 4) ∨ w = (m + 6) := by
      simp [upperQuadrupleResidual] at hw
      omega
    rcases hcases with rfl | rfl
    · apply Position.value_ne_loss_of_exact_sum_residuals _ {4, m} _ m
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [upperQuadrupleResidual]
        omega
      · simp [show 4 ≠ m by omega]
        omega
      · intro w hw hgt
        have hcases : w = (m + 6) := by
          simp [upperQuadrupleResidual] at hw
          omega
        subst w
        apply Position.value_ne_loss_of_exact_sum_residuals _ {7, (m - 1)} _ (m - 1)
        · simp
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          omega
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp [upperQuadrupleResidual]
          omega
        · simp [show 7 ≠ (m - 1) by omega]
          omega
        · intro w hw hgt
          simp [upperQuadrupleResidual] at hw
          omega
    · apply Position.value_ne_loss_of_exact_sum_residuals _ {6, m} _ m
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [upperQuadrupleResidual]
        omega
      · simp [show 6 ≠ m by omega]
        omega
      · intro w hw hgt
        have hcases : w = (m + 4) := by
          simp [upperQuadrupleResidual] at hw
          omega
        subst w
        apply Position.value_ne_loss_of_exact_sum_residuals _ {5, (m - 1)} _ (m - 1)
        · simp
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          omega
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp [upperQuadrupleResidual]
          omega
        · simp [show 5 ≠ (m - 1) by omega]
          omega
        · intro w hw hgt
          simp [upperQuadrupleResidual] at hw
          omega

/-- Exclusion of upper opening 6 in the four-counter tail. -/
theorem upper_quadruple_last_opening_ne_loss (m : ℕ) (hm : 17 ≤ m) :
    (afterOpening (upperQuadrupleResidual m) (m + 6)).value ≠ .loss := by
  apply Position.value_ne_loss_of_exact_sum_residuals _ {2, (m + 4)} _ (m + 4)
  · simp
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp [upperQuadrupleResidual]
    omega
  · simp
    omega
  · intro w hw hgt
    have hcases : w = (m + 5) := by
      simp [upperQuadrupleResidual] at hw
      omega
    subst w
    apply Position.value_ne_loss_of_exact_sum_residuals _ {5, m} _ m
    · simp
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      omega
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp [upperQuadrupleResidual]
      omega
    · simp [show 5 ≠ m by omega]
      omega
    · intro w hw hgt
      have hcases : w = (m + 3) := by
        simp [upperQuadrupleResidual] at hw
        omega
      subst w
      apply Position.value_ne_loss_of_exact_sum_residuals _ {4, (m - 1)} _ (m - 1)
      · simp
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp [upperQuadrupleResidual]
        omega
      · simp [show 4 ≠ (m - 1) by omega]
        omega
      · intro w hw hgt
        simp [upperQuadrupleResidual] at hw
        omega

/-- The fifth-from-top lower-ray position is nonlosing for every $N \ge 23$. -/
theorem pair_deletion_position_fifth_from_top_value_ne_loss (N : ℕ) (hN : 23 ≤ N) :
    (pairDeletionPosition N 1 (N - 4)).value ≠ .loss := by
  apply pair_deletion_position_value_ne_loss_of_upper_residuals N (N - 4)
    (by omega) (by omega)
  intro y hy
  have hres : ((((Finset.Icc 1 N).erase 1).erase (N - 4)).erase (N - 4 - 1)) =
      upperQuadrupleResidual (N - 6) := by
    ext x
    simp [upperQuadrupleResidual]
    omega
  rw [hres]
  have hcases : y = (N - 6) + 3 ∨ y = (N - 6) + 4 ∨
      y = (N - 6) + 5 ∨ y = (N - 6) + 6 := by
    simp only [Finset.mem_Icc] at hy
    omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact upper_quadruple_first_opening_ne_loss _ (by omega)
  · exact upper_quadruple_second_opening_ne_loss _ (by omega)
  · exact upper_quadruple_third_opening_ne_loss _ (by omega)
  · exact upper_quadruple_last_opening_ne_loss _ (by omega)

end CatchUp
