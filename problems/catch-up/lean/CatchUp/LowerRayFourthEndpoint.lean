/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/LowerRayFourthEndpoint.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.ExactSumResiduals
public import CatchUp.Earlier.DeficitWinningBound
public import CatchUp.CompletedTurn
public import CatchUp.Classifier

/-!
# Fourth-from-top lower-ray nonloss by exact-sum exchange

The exact-sum loss obstruction forces a larger winning opening after each chosen
block. A finite symbolic tree excludes all three upper openings of
`[2,m] ∪ {m+3,m+4,m+5}`. Each terminal branch has a dominating exact-sum
block, except for one explicit completed-turn repair at `m=10`.

The result needs no smaller-interval draw hypothesis. The range below fifteen
uses four small kernel evaluations of the existing safety classifier. No outcome
tables, conjecture assumptions, or native evaluation are used in the proofs.

The structural inputs are `CatchUp.ExactSumLossObstruction`,
`CatchUp.Earlier.DeficitWinningBound`, and `CatchUp.CompletedTurn`.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- A two-counter specialization of exact-sum residual exclusion. -/
theorem Position.value_ne_loss_of_exact_pair_residuals (S : Finset ℕ) (d a c : ℕ)
    (ha : a ∈ S) (hc : c ∈ S) (hap : 0 < a) (hcp : 0 < c)
    (hac : a ≠ c) (hsum : a + c = d)
    (hnext : ∀ w ∈ S \ {a,c}, c < w →
      (afterOpening (S \ {a,c}) w).value ≠ .loss) :
    (⟨S,d⟩ : Position).value ≠ .loss := by
  intro hloss
  obtain ⟨w, hw, hl, hgt⟩ :=
    Position.exists_winning_opening_gt_max_of_loss_of_exact_sum S {a,c} d
      (by simp) (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                    rcases hx with rfl | rfl <;> omega)
      (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
      (by simp [hac, hsum]) hloss
  have hcm : c ≤ ({a,c} : Finset ℕ).max' (by simp) :=
    Finset.le_max' _ _ (by simp)
  exact hnext w hw (by omega) hl

/-- The lower interval with a two-counter gap followed by three consecutive top counters. -/
def upperTripleResidual (m : ℕ) : Finset ℕ := Finset.Icc 2 m ∪ {m+3,m+4,m+5}

/-- The completed turn with counters two, six, and fifteen gives a terminal losing endpoint. -/
theorem upper_triple_five_counter_repair :
    (⟨{2,3,6,7,15},9⟩ : Position).value ≠ .loss := by
  apply (Position.value_ne_loss_iff_exists_completed_turn_subset _
    (by decide) (by decide)).2
  refine ⟨{2,6,15}, by simp, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · have heq :
        (completedTurnEndpoint ⟨(⟨{2,3,6,7,15},9⟩ : Position), .p1⟩
          {2,6,15}).toPosition = ⟨{3,7},14⟩ := by decide
    rw [heq, Position.value.eq_def]
    simp

/-- The middle top opening is nonlosing when the lower interval extends through at least ten. -/
theorem upper_triple_middle_opening_ne_loss (m : ℕ) (hm : 10 ≤ m) :
    (afterOpening (upperTripleResidual m) (m+4)).value ≠ .loss := by
  apply Position.value_ne_loss_of_exact_pair_residuals _ _ 4 m
  · simp [upperTripleResidual]; omega
  · simp [upperTripleResidual]; omega
  · omega
  · omega
  · omega
  · omega
  · intro w hw hgt
    have hwcases : w = m+3 ∨ w = m+5 := by
      simp [upperTripleResidual] at hw
      omega
    rcases hwcases with rfl | rfl
    · apply Position.value_ne_loss_of_exact_pair_residuals _ _ 5 (m-2)
      · simp [upperTripleResidual]; omega
      · simp [upperTripleResidual]; omega
      · omega
      · omega
      · omega
      · omega
      · intro v hv hvg
        have hvcases : v = m-1 ∨ v = m+5 := by
          simp [upperTripleResidual] at hv
          omega
        rcases hvcases with rfl | rfl
        · by_cases hm10 : m = 10
          · subst m
            have heq :
                afterOpening
                  (((upperTripleResidual 10).erase (10+4) \ {4,10}).erase (10+3) \ {5,10-2})
                  (10-1) = (⟨{2,3,6,7,15},9⟩ : Position) := by
              decide
            rw [heq]
            exact upper_triple_five_counter_repair
          have hm11 : 11 ≤ m := by omega
          apply Position.value_ne_loss_of_exact_pair_residuals _ _ 2 (m-3)
          · simp [upperTripleResidual]; omega
          · simp [upperTripleResidual]; omega
          · omega
          · omega
          · omega
          · omega
          · intro u hu hug
            have hueq : u = m+5 := by
              simp [upperTripleResidual] at hu
              omega
            subst u
            apply Position.value_ne_loss_of_exact_sum_residuals _ {3,6,m-4} _ (m-4)
            · simp
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              omega
            · intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              simp [upperTripleResidual]
              omega
            · simp [show 6 ≠ m-4 by omega, show 3 ≠ m-4 by omega]
              omega
            · intro z hz hzg
              simp [upperTripleResidual] at hz
              omega
        · apply Position.value_ne_loss_of_exact_pair_residuals _ _ 6 (m-1)
          · simp [upperTripleResidual]; omega
          · simp [upperTripleResidual]; omega
          · omega
          · omega
          · omega
          · omega
          · intro z hz hzg
            simp [upperTripleResidual] at hz
            omega
    · apply Position.value_ne_loss_of_exact_pair_residuals _ _ 2 (m+3)
      · simp [upperTripleResidual]; omega
      · simp [upperTripleResidual]; omega
      · omega
      · omega
      · omega
      · omega
      · intro z hz hzg
        simp [upperTripleResidual] at hz
        omega

/-- The largest top opening is nonlosing when the lower interval extends through at least six. -/
theorem upper_triple_last_opening_ne_loss (m : ℕ) (hm : 6 ≤ m) :
    (afterOpening (upperTripleResidual m) (m+5)).value ≠ .loss := by
  apply Position.value_ne_loss_of_exact_pair_residuals _ _ 2 (m+3)
  · simp [upperTripleResidual]; omega
  · simp [upperTripleResidual]
  · omega
  · omega
  · omega
  · omega
  · intro w hw hgt
    have heq : w = m+4 := by simp [upperTripleResidual] at hw; omega
    subst w
    apply Position.value_ne_loss_of_exact_pair_residuals _ _ 4 m
    · simp [upperTripleResidual]; omega
    · simp [upperTripleResidual]; omega
    · omega
    · omega
    · omega
    · omega
    · intro z hz hzg
      simp [upperTripleResidual] at hz
      omega

/-- The smallest top opening is nonlosing when the lower interval extends through at least ten. -/
theorem upper_triple_first_opening_ne_loss (m : ℕ) (hm : 10 ≤ m) :
    (afterOpening (upperTripleResidual m) (m+3)).value ≠ .loss := by
  apply Position.value_ne_loss_of_exact_pair_residuals _ _ 3 m
  · simp [upperTripleResidual]; omega
  · simp [upperTripleResidual]; omega
  · omega
  · omega
  · omega
  · omega
  · intro w hw hgt
    have hcases : w = m+4 ∨ w = m+5 := by simp [upperTripleResidual] at hw; omega
    rcases hcases with rfl | rfl
    · apply Position.value_ne_loss_of_exact_pair_residuals _ _ 5 (m-1)
      · simp [upperTripleResidual]; omega
      · simp [upperTripleResidual]; omega
      · omega
      · omega
      · omega
      · omega
      · intro v hv hvg
        have heq : v = m+5 := by simp [upperTripleResidual] at hv; omega
        subst v
        apply Position.value_ne_loss_of_exact_pair_residuals _ _ 7 (m-2)
        · simp [upperTripleResidual]; omega
        · simp [upperTripleResidual]; omega
        · omega
        · omega
        · omega
        · omega
        · intro z hz hzg
          simp [upperTripleResidual] at hz
          omega
    · apply Position.value_ne_loss_of_exact_pair_residuals _ _ 6 (m-1)
      · simp [upperTripleResidual]; omega
      · simp [upperTripleResidual]; omega
      · omega
      · omega
      · omega
      · omega
      · intro v hv hvg
        have heq : v = m+4 := by simp [upperTripleResidual] at hv; omega
        subst v
        apply Position.value_ne_loss_of_exact_sum_residuals _ {2,4,m-2} _ (m-2)
        · simp
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          omega
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp [upperTripleResidual]
          omega
        · simp [show 4 ≠ m-2 by omega, show 2 ≠ m-2 by omega]
          omega
        · intro z hz hzg
          simp [upperTripleResidual] at hz
          omega

private theorem nonloss_of_check (p : Position)
    (h : CatchUpSearch.CanAvoidLossClassifier.check .p1 ⟨p,.p1⟩ = true) :
    p.value ≠ .loss := by
  have hsafe := (CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff .p1 ⟨p,.p1⟩).mp h
  simpa using (can_avoid_loss_iff_value .p1 ⟨p,.p1⟩).mp hsafe

/-- Kernel-checked small exceptions for the first upper opening. -/
theorem upper_triple_small_first_opening_ne_loss (m : ℕ) (hm : m = 6 ∨ m = 7) :
    (afterOpening (upperTripleResidual m) (m+3)).value ≠ .loss := by
  rcases hm with rfl | rfl
  all_goals
    apply nonloss_of_check
    decide +kernel

/-- Kernel-checked small exceptions for the middle upper opening. -/
theorem upper_triple_small_middle_opening_ne_loss (m : ℕ) (hm : m = 6 ∨ m = 7) :
    (afterOpening (upperTripleResidual m) (m+4)).value ≠ .loss := by
  rcases hm with rfl | rfl
  all_goals
    apply nonloss_of_check
    decide +kernel

/-- The fourth-from-top lower-ray position is nonlosing at every size at least fifteen. -/
theorem pair_deletion_position_fourth_from_top_value_ne_loss_of_fifteen_le (N : ℕ) (hN : 15 ≤ N) :
    (pairDeletionPosition N 1 (N-3)).value ≠ .loss := by
  apply pair_deletion_position_value_ne_loss_of_upper_residuals N (N-3)
    (by omega) (by omega)
  intro y hy
  have hres : (((Finset.Icc 1 N).erase 1).erase (N-3)).erase (N-3-1) =
      upperTripleResidual (N-5) := by
    ext x
    simp [upperTripleResidual]
    omega
  rw [hres]
  have hcases : y = (N-5)+3 ∨ y = (N-5)+4 ∨ y = (N-5)+5 := by
    simp only [Finset.mem_Icc] at hy
    omega
  rcases hcases with rfl | rfl | rfl
  · exact upper_triple_first_opening_ne_loss _ (by omega)
  · exact upper_triple_middle_opening_ne_loss _ (by omega)
  · exact upper_triple_last_opening_ne_loss _ (by omega)

/-- The fourth-from-top lower-ray position is nonlosing throughout the requested even-total range. -/
theorem pair_deletion_position_fourth_from_top_value_ne_loss (N : ℕ) (hN : 11 ≤ N)
    (heven : Even (N*(N+1)/2)) :
    (pairDeletionPosition N 1 (N-3)).value ≠ .loss := by
  by_cases hlarge : 15 ≤ N
  · exact pair_deletion_position_fourth_from_top_value_ne_loss_of_fifteen_le N hlarge
  have hcases : N = 11 ∨ N = 12 := by
    interval_cases N <;> first | omega | norm_num at heven
  apply pair_deletion_position_value_ne_loss_of_upper_residuals N (N-3)
    (by omega) (by omega)
  intro y hy
  have hres : (((Finset.Icc 1 N).erase 1).erase (N-3)).erase (N-3-1) =
      upperTripleResidual (N-5) := by
    ext x
    simp [upperTripleResidual]
    omega
  rw [hres]
  have hym : y = (N-5)+3 ∨ y = (N-5)+4 ∨ y = (N-5)+5 := by
    simp only [Finset.mem_Icc] at hy
    omega
  rcases hym with rfl | rfl | rfl
  · exact upper_triple_small_first_opening_ne_loss _ (by omega)
  · exact upper_triple_small_middle_opening_ne_loss _ (by omega)
  · exact upper_triple_last_opening_ne_loss _ (by omega)

end CatchUp
