/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/RootUpperEightCriterion.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.RootUpperEightFrontier

/-!
# An exact all-reply criterion for the actual eight-shadow

With the losing eight-shadow retained, the reserve-five endpoint wins exactly
when the two-anchor core loses at deficit one. This is a conditional criterion;
the core's nonloss and the interval conjecture remain open.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.RootUpperEightCriterion

open CatchUp (Position.value_eq_loss_iff_of_nonterminal)
/-- Copy of `CatchUp.WinningOpening`'s private lemma; public, its name would clash with
`CatchUp.Best`'s differently stated one. -/
private theorem Outcome.best_eq_win_iff (outcomes : List Outcome) :
    Outcome.best outcomes = .win ↔ ∃ outcome ∈ outcomes, outcome = .win := by
  rw [← not_iff_not]
  simp
  constructor
  · intro hall hmem
    exact hall .win hmem rfl
  · intro hnot outcome hmem heq
    subst outcome
    exact hnot hmem

/-- With equality counter five absent, the low-two loss is exactly the core-one loss. -/
theorem low_two_loss_iff_core_one_loss (C : Finset ℕ)
    (h2 : 2 ∈ C) (h3 : 3 ∈ C) (hmin : ∀ x ∈ C, 2 ≤ x) (h5 : 5 ∉ C)
    (hhigh : (⟨C, 8⟩ : Position).value = .loss) :
    (⟨C, 2⟩ : Position).value = .loss ↔
      (⟨C \ {2, 3}, 1⟩ : Position).value = .loss := by
  constructor
  · exact RootUpperEightFrontier.core_one_loss_of_low_two_loss C h2 h3 hmin hhigh
  · intro hcore
    have h2D : 2 ∈ C.erase 3 := by simp [h2]
    have hset : (C.erase 3).erase 2 = C \ {2, 3} := by
      ext x
      simp [and_comm, and_left_comm]
    have hcatchD : ¬ (C.erase 3).sum (fun x ↦ x) < 1 := by
      have hs := Finset.single_le_sum (f := fun x : ℕ ↦ x)
        (fun _ _ ↦ Nat.zero_le _) h2D
      change 2 ≤ (C.erase 3).sum (fun x ↦ x) at hs
      omega
    have hDwin : (⟨C.erase 3, 1⟩ : Position).value = .win := by
      rw [Position.value_eq_best_move_outcome _ (Finset.ne_empty_of_mem h2D) hcatchD,
        Outcome.best_eq_win_iff]
      refine ⟨(⟨C.erase 3, 1⟩ : Position).moveOutcome 2,
        List.mem_map.mpr ⟨⟨2, h2D⟩, by simp, rfl⟩, ?_⟩
      simp [Position.moveOutcome, Position.afterPick, hset, hcore, Outcome.neg]
    have hcatchC : ¬ C.sum (fun x ↦ x) < 2 := by
      exact not_lt.mpr (Finset.single_le_sum (f := fun x : ℕ ↦ x)
        (fun _ _ ↦ Nat.zero_le _) h2)
    apply (Position.value_eq_loss_iff_of_nonterminal ⟨C, 2⟩
      ⟨Finset.ne_empty_of_mem h2, hcatchC⟩).mpr
    intro x hx
    by_cases hx3 : x = 3
    · subst x
      simp [Position.moveOutcome, Position.afterPick, hDwin, Outcome.neg]
    · exact DeficitCrossingEntry.eight_to_two_first_move C x h3 hmin h5 hhigh hx hx3

/-- The reserve-five endpoint wins exactly when the core loses at deficit one. -/
theorem reserve_five_win_iff_core_one_loss (C : Finset ℕ)
    (h2 : 2 ∈ C) (h3 : 3 ∈ C) (hmin : ∀ x ∈ C, 2 ≤ x)
    (h5 : 5 ∉ C) (h6 : 6 ∉ C) (h8 : 8 ∉ C)
    (hhigh : (⟨C, 8⟩ : Position).value = .loss) :
    (⟨insert 5 C, 3⟩ : Position).value = .win ↔
      (⟨C \ {2, 3}, 1⟩ : Position).value = .loss := by
  constructor
  · intro hwin
    exact (RootUpperEightFrontier.core_double_loss_of_low_loss C h2 h3 hmin hhigh
      (RootUpperEightFrontier.low_loss_of_reserve_win C hmin h5 h6 h8 hhigh hwin)).1
  · intro hcore
    have hlow := (low_two_loss_iff_core_one_loss C h2 h3 hmin h5 hhigh).mpr hcore
    have hcatch : ¬ (insert 5 C).sum (fun x ↦ x) < 3 := by
      have hs := Finset.single_le_sum (f := fun x : ℕ ↦ x)
        (fun _ _ ↦ Nat.zero_le _) (show 5 ∈ insert 5 C by simp)
      change 5 ≤ (insert 5 C).sum (fun x ↦ x) at hs
      omega
    rw [Position.value_eq_best_move_outcome _ (by simp) hcatch, Outcome.best_eq_win_iff]
    refine ⟨(⟨insert 5 C, 3⟩ : Position).moveOutcome 5,
      List.mem_map.mpr ⟨⟨5, by simp⟩, by simp, rfl⟩, ?_⟩
    simp [Position.moveOutcome, Position.afterPick, h5, hlow, Outcome.neg]

/-- Exact all-reply nonwinning criterion, with the losing eight-shadow retained. -/
theorem reserve_five_nonwin_iff_core_nonloss (C : Finset ℕ)
    (h2 : 2 ∈ C) (h3 : 3 ∈ C) (hmin : ∀ x ∈ C, 2 ≤ x)
    (h5 : 5 ∉ C) (h6 : 6 ∉ C) (h8 : 8 ∉ C)
    (hhigh : (⟨C, 8⟩ : Position).value = .loss) :
    (⟨insert 5 C, 3⟩ : Position).value ≠ .win ↔
      (⟨C \ {2, 3}, 1⟩ : Position).value ≠ .loss := by
  exact not_congr (reserve_five_win_iff_core_one_loss C h2 h3 hmin h5 h6 h8 hhigh)

/-- At the actual interval endpoint after parent pick eight, core nonloss is
necessary and sufficient for nonwinning, conditional on the actual eight-shadow loss. -/
theorem interval_reserve_nonwin_iff_core_nonloss (N : ℕ) (hN : 11 ≤ N)
    (hhigh : (⟨Icc 2 N \ {5, 6, 8}, 8⟩ : Position).value = .loss) :
    (⟨Icc 2 N \ {6, 8}, 3⟩ : Position).value ≠ .win ↔
      (⟨{4, 7} ∪ Icc 9 N, 1⟩ : Position).value ≠ .loss := by
  let C := Icc 2 N \ {5, 6, 8}
  have h2 : 2 ∈ C := by simp [C]; omega
  have h3 : 3 ∈ C := by simp [C]; omega
  have hmin : ∀ x ∈ C, 2 ≤ x := by
    intro x hx
    exact (mem_Icc.mp (mem_sdiff.mp hx).1).1
  have h5 : 5 ∉ C := by simp [C]
  have h6 : 6 ∉ C := by simp [C]
  have h8 : 8 ∉ C := by simp [C]
  have hR : insert 5 C = Icc 2 N \ {6, 8} := by
    ext x
    simp only [C, mem_insert, mem_sdiff, mem_Icc, mem_singleton]
    omega
  have hE : C \ {2, 3} = {4, 7} ∪ Icc 9 N := by
    ext x
    simp only [C, mem_union, mem_insert, mem_sdiff, mem_Icc, mem_singleton]
    omega
  simpa only [hR, hE] using reserve_five_nonwin_iff_core_nonloss C h2 h3 hmin
    h5 h6 h8 hhigh

end CatchUp.RootUpperEightCriterion
