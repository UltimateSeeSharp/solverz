/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/PairClassification.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Reference

/-!
# Symbolic classification of the Catch-Up top-four endgame

This module classifies positions whose remaining counters are exactly the four consecutive counters
added in the passage from game size `N` to `N + 4`.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.TopFourClassification

open CatchUp

theorem value_empty (deficit : ℕ) :
    Position.value ⟨∅, deficit⟩ = if deficit = 0 then .draw else .loss := by
  rw [Position.value.eq_def]
  simp

theorem best_eq_win_iff (outcomes : List Outcome) :
    Outcome.best outcomes = .win ↔ ∃ outcome ∈ outcomes, outcome = .win := by
  rw [← not_iff_not]
  simp
  constructor
  · intro hall hmem
    exact hall .win hmem rfl
  · intro hnot outcome hmem heq
    subst outcome
    exact hnot hmem

theorem best_eq_loss_iff (outcomes : List Outcome) :
    Outcome.best outcomes = .loss ↔ ∀ outcome ∈ outcomes, outcome = .loss := by
  rw [← not_iff_not]
  simp

theorem value_eq_win_iff (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬position.remaining.sum (fun x => x) < position.deficit) :
    position.value = .win ↔
      ∃ x ∈ position.remaining, position.moveOutcome x = .win := by
  rw [Position.value_eq_best_move_outcome position hremaining hcatch, best_eq_win_iff]
  simp [Position.moveOutcome]

theorem value_eq_loss_iff (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬position.remaining.sum (fun x => x) < position.deficit) :
    position.value = .loss ↔
      ∀ x ∈ position.remaining, position.moveOutcome x = .loss := by
  rw [Position.value_eq_best_move_outcome position hremaining hcatch, best_eq_loss_iff]
  simp [Position.moveOutcome]

theorem value_eq_draw_iff (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬position.remaining.sum (fun x => x) < position.deficit) :
    position.value = .draw ↔
      (∃ x ∈ position.remaining, position.moveOutcome x ≠ .loss) ∧
      ∀ x ∈ position.remaining, position.moveOutcome x ≠ .win := by
  rw [Position.value_eq_best_move_outcome position hremaining hcatch, Outcome.eq_draw_iff,
    Outcome.best_ne_loss_iff, Outcome.best_ne_win_iff]
  simp [Position.moveOutcome]

theorem value_singleton (counter deficit : ℕ) :
    Position.value ⟨{counter}, deficit⟩ =
      if deficit < counter then .win else if deficit = counter then .draw else .loss := by
  by_cases hterminal : counter < deficit
  · rw [Position.value.eq_def]
    have hnot : ¬deficit < counter := by omega
    have hne : deficit ≠ counter := by omega
    simp [hterminal, hnot, hne]
  · have hle : deficit ≤ counter := by omega
    by_cases heq : deficit = counter
    · subst deficit
      rw [ite_eq_right (Nat.lt_irrefl counter), ite_eq_left rfl]
      apply (value_eq_draw_iff ⟨{counter}, counter⟩ (by simp) (by simp)).2
      simp [Position.moveOutcome, Position.afterPick, value_empty, Outcome.neg]
    · have hlt : deficit < counter := by omega
      rw [ite_eq_left hlt]
      apply (value_eq_win_iff ⟨{counter}, deficit⟩ (by simp) (by simp [hle])).2
      refine ⟨counter, by simp, ?_⟩
      have hdiff : counter - deficit ≠ 0 := by omega
      simp [Position.moveOutcome, Position.afterPick, hterminal, value_empty, hdiff, Outcome.neg]

def pairFormula (lower upper deficit : ℕ) : Outcome :=
  if deficit < upper - lower then .win
  else if deficit = upper - lower then .draw
  else if deficit ≤ lower then .loss
  else .win

theorem value_pair (lower upper deficit : ℕ)
    (hlowerPos : 0 < lower) (hlowerUpper : lower < upper)
    (hgapLower : upper - lower ≤ lower) (hdeficit : deficit ≤ upper) :
    Position.value ⟨{lower, upper}, deficit⟩ = pairFormula lower upper deficit := by
  have hremaining : ({lower, upper} : Finset ℕ) ≠ ∅ := by simp
  have hcatch : ¬∑ x ∈ ({lower, upper} : Finset ℕ), x < deficit := by
    simp [ne_of_lt hlowerUpper]
    omega
  have heraseLower : ({lower, upper} : Finset ℕ).erase lower = {upper} := by
    ext x
    simp
    omega
  have heraseUpper : ({lower, upper} : Finset ℕ).erase upper = {lower} := by
    ext x
    simp
    omega
  unfold pairFormula
  split_ifs with hgap hgapEq hlower
  · apply (value_eq_win_iff ⟨{lower, upper}, deficit⟩ hremaining hcatch).2
    refine ⟨upper, by simp, ?_⟩
    have hnotCatch : ¬upper < deficit := by omega
    have hchildNotLt : ¬upper - deficit < lower := by omega
    have hchildNe : upper - deficit ≠ lower := by omega
    simp only [Position.moveOutcome, Position.afterPick, hnotCatch, ite_false]
    rw [heraseUpper, value_singleton]
    simp [hchildNotLt, hchildNe, Outcome.neg]
  · apply (value_eq_draw_iff ⟨{lower, upper}, deficit⟩ hremaining hcatch).2
    have hnotLower : ¬lower < deficit := by omega
    have hnotUpper : ¬upper < deficit := by omega
    have hlowerChildLt : lower - deficit < upper := by omega
    have hupperChildEq : upper - deficit = lower := by omega
    have hlowerMove :
        (⟨{lower, upper}, deficit⟩ : Position).moveOutcome lower = .loss := by
      simp only [Position.moveOutcome, Position.afterPick, hnotLower, ite_false]
      rw [heraseLower, value_singleton]
      simp [hlowerChildLt, Outcome.neg]
    have hupperMove :
        (⟨{lower, upper}, deficit⟩ : Position).moveOutcome upper = .draw := by
      simp only [Position.moveOutcome, Position.afterPick, hnotUpper, ite_false]
      rw [heraseUpper, value_singleton]
      simp [hupperChildEq, Outcome.neg]
    constructor
    · exact ⟨upper, by simp, by simp [hupperMove]⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp [hlowerMove]
      · simp [hupperMove]
  · apply (value_eq_loss_iff ⟨{lower, upper}, deficit⟩ hremaining hcatch).2
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · subst x
      have hnotLower : ¬lower < deficit := by omega
      have hchildLt : lower - deficit < upper := by omega
      simp only [Position.moveOutcome, Position.afterPick, hnotLower, ite_false]
      rw [heraseLower, value_singleton]
      simp [hchildLt, Outcome.neg]
    · subst x
      have hnotUpper : ¬upper < deficit := by omega
      have hchildLt : upper - deficit < lower := by omega
      simp only [Position.moveOutcome, Position.afterPick, hnotUpper, ite_false]
      rw [heraseUpper, value_singleton]
      simp [hchildLt, Outcome.neg]
  · apply (value_eq_win_iff ⟨{lower, upper}, deficit⟩ hremaining hcatch).2
    refine ⟨lower, by simp, ?_⟩
    have hcontinue : lower < deficit := by omega
    have hchildLt : deficit - lower < upper := by omega
    simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_true]
    rw [heraseLower, value_singleton]
    simp [hchildLt]

def pairFormulaExact (lower upper deficit : ℕ) : Outcome :=
  if deficit < upper - lower then .win
  else if deficit = upper - lower then .draw
  else if deficit ≤ lower then .loss
  else if deficit < lower + upper then .win
  else if deficit = lower + upper then .draw
  else .loss

/-- Exact normalized value of two close positive counters at every deficit. -/
theorem value_pair_exact (lower upper deficit : ℕ)
    (hlowerPos : 0 < lower) (hlowerUpper : lower < upper)
    (hgapLower : upper - lower ≤ lower) :
    Position.value ⟨{lower, upper}, deficit⟩ = pairFormulaExact lower upper deficit := by
  by_cases hle : deficit ≤ upper
  · rw [value_pair lower upper deficit hlowerPos hlowerUpper hgapLower hle]
    have hsum : deficit < lower + upper := by omega
    unfold pairFormula pairFormulaExact
    split_ifs <;> simp_all
  · have hremaining : ({lower, upper} : Finset ℕ) ≠ ∅ := by simp
    have hlowerLt : lower < deficit := by omega
    have hupperLt : upper < deficit := by omega
    have hgapLt : upper - lower < deficit := lt_of_le_of_lt hgapLower hlowerLt
    have hnotGapLt : ¬deficit < upper - lower := not_lt_of_ge hgapLt.le
    have hnotGapEq : deficit ≠ upper - lower := ne_of_gt hgapLt
    have hnotLowerLe : ¬deficit ≤ lower := not_le_of_gt hlowerLt
    have heraseLower : ({lower, upper} : Finset ℕ).erase lower = {upper} := by
      ext x
      simp
      omega
    have heraseUpper : ({lower, upper} : Finset ℕ).erase upper = {lower} := by
      ext x
      simp
      omega
    by_cases hsumLt : deficit < lower + upper
    · have hformula : pairFormulaExact lower upper deficit = .win := by
        unfold pairFormulaExact
        rw [ite_eq_right hnotGapLt, ite_eq_right hnotGapEq, ite_eq_right hnotLowerLe, ite_eq_left hsumLt]
      rw [hformula]
      have hcatch : ¬∑ x ∈ ({lower, upper} : Finset ℕ), x < deficit := by
        simp [ne_of_lt hlowerUpper]
        omega
      apply (value_eq_win_iff ⟨{lower, upper}, deficit⟩ hremaining hcatch).2
      refine ⟨lower, by simp, ?_⟩
      have hchildLt : deficit - lower < upper := by omega
      simp only [Position.moveOutcome, Position.afterPick, hlowerLt, ite_true]
      rw [heraseLower, value_singleton]
      simp [hchildLt]
    · by_cases hsumEq : deficit = lower + upper
      · have hformula : pairFormulaExact lower upper deficit = .draw := by
          unfold pairFormulaExact
          rw [ite_eq_right hnotGapLt, ite_eq_right hnotGapEq, ite_eq_right hnotLowerLe, ite_eq_right hsumLt,
            ite_eq_left hsumEq]
        rw [hformula]
        have hcatch : ¬∑ x ∈ ({lower, upper} : Finset ℕ), x < deficit := by
          simp [ne_of_lt hlowerUpper]
          omega
        apply (value_eq_draw_iff ⟨{lower, upper}, deficit⟩ hremaining hcatch).2
        have hlowerChildEq : deficit - lower = upper := by omega
        have hupperChildEq : deficit - upper = lower := by omega
        have hlowerMove :
            (⟨{lower, upper}, deficit⟩ : Position).moveOutcome lower = .draw := by
          simp only [Position.moveOutcome, Position.afterPick, hlowerLt, ite_true]
          rw [heraseLower, value_singleton]
          simp [hlowerChildEq]
        have hupperMove :
            (⟨{lower, upper}, deficit⟩ : Position).moveOutcome upper = .draw := by
          simp only [Position.moveOutcome, Position.afterPick, hupperLt, ite_true]
          rw [heraseUpper, value_singleton]
          simp [hupperChildEq]
        constructor
        · exact ⟨lower, by simp, by simp [hlowerMove]⟩
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with hx | hx
          · subst x
            simp [hlowerMove]
          · subst x
            simp [hupperMove]
      · have hsumTerminal : lower + upper < deficit := by omega
        have hformula : pairFormulaExact lower upper deficit = .loss := by
          unfold pairFormulaExact
          rw [ite_eq_right hnotGapLt, ite_eq_right hnotGapEq, ite_eq_right hnotLowerLe, ite_eq_right hsumLt,
            ite_eq_right hsumEq]
        rw [hformula, Position.value.eq_def]
        simp [ne_of_lt hlowerUpper, hsumTerminal]


end CatchUpSearch.TopFourClassification
