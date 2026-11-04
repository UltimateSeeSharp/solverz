/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/TopFourClassification.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates; its
copies of CatchUp.PairClassification's helpers dropped.
-/
module

public import Mathlib
public import CatchUp.Reference
public import CatchUp.PairClassification

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

/-- Exact normalized value of two close positive counters at every deficit. -/
theorem earlier_value_pair_exact (lower upper deficit : ℕ)
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

private theorem move_outcome_eq_pair_formula_exact (remaining : Finset ℕ)
    (chosen lower upper deficit : ℕ)
    (herase : remaining.erase chosen = {lower, upper})
    (hlowerPos : 0 < lower) (hlowerUpper : lower < upper)
    (hgapLower : upper - lower ≤ lower) :
    (⟨remaining, deficit⟩ : Position).moveOutcome chosen =
      if chosen < deficit then pairFormulaExact lower upper (deficit - chosen)
      else (pairFormulaExact lower upper (chosen - deficit)).neg := by
  by_cases hcontinue : chosen < deficit
  · rw [ite_eq_left hcontinue]
    simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_true]
    rw [herase, earlier_value_pair_exact lower upper (deficit - chosen) hlowerPos hlowerUpper hgapLower]
  · rw [ite_eq_right hcontinue]
    simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_false]
    rw [herase, earlier_value_pair_exact lower upper (chosen - deficit) hlowerPos hlowerUpper hgapLower]

def tripleWithoutFirstFormula (a deficit : ℕ) : Outcome :=
  if deficit = a + 2 then .draw else .win

/-- Exact value of the upper three counters after deleting the first of four consecutive counters. -/
theorem value_triple_without_first (a deficit : ℕ) (ha : 5 ≤ a) (hdeficit : deficit ≤ a + 3) :
    Position.value ⟨{a + 1, a + 2, a + 3}, deficit⟩ =
      tripleWithoutFirstFormula a deficit := by
  let remaining : Finset ℕ := {a + 1, a + 2, a + 3}
  have hremaining : remaining ≠ ∅ := by simp [remaining]
  have hcatch : ¬remaining.sum (fun counter => counter) < deficit := by
    simp [remaining]
    omega
  have heraseFirst : remaining.erase (a + 1) = {a + 2, a + 3} := by
    ext counter
    simp [remaining]
  have heraseSecond : remaining.erase (a + 2) = {a + 1, a + 3} := by
    ext counter
    simp [remaining]
    omega
  have heraseThird : remaining.erase (a + 3) = {a + 1, a + 2} := by
    ext counter
    simp [remaining]
    omega
  have hmoveFirst := move_outcome_eq_pair_formula_exact remaining (a + 1) (a + 2) (a + 3)
    deficit heraseFirst (by omega) (by omega) (by omega)
  have hmoveSecond := move_outcome_eq_pair_formula_exact remaining (a + 2) (a + 1) (a + 3)
    deficit heraseSecond (by omega) (by omega) (by omega)
  have hmoveThird := move_outcome_eq_pair_formula_exact remaining (a + 3) (a + 1) (a + 2)
    deficit heraseThird (by omega) (by omega) (by omega)
  unfold tripleWithoutFirstFormula
  by_cases hdraw : deficit = a + 2
  · rw [ite_eq_left hdraw]
    subst deficit
    have hfirstDraw :
        (⟨remaining, a + 2⟩ : Position).moveOutcome (a + 1) = .draw := by
      rw [hmoveFirst]
      simp [pairFormulaExact]
    have hsecondLoss :
        (⟨remaining, a + 2⟩ : Position).moveOutcome (a + 2) = .loss := by
      rw [hmoveSecond]
      simp [pairFormulaExact, Outcome.neg]
    have hthirdDraw :
        (⟨remaining, a + 2⟩ : Position).moveOutcome (a + 3) = .draw := by
      rw [hmoveThird]
      simp [pairFormulaExact, Outcome.neg]
    apply (value_eq_draw_iff ⟨remaining, a + 2⟩ hremaining hcatch).2
    constructor
    · exact ⟨a + 1, by simp [remaining], by simp [hfirstDraw]⟩
    · intro counter hcounter
      simp only [remaining, Finset.mem_insert, Finset.mem_singleton] at hcounter
      rcases hcounter with hcounter | hcounter | hcounter
      · subst counter
        simp [hfirstDraw]
      · subst counter
        simp [hsecondLoss]
      · subst counter
        simp [hthirdDraw]
  · rw [ite_eq_right hdraw]
    apply (value_eq_win_iff ⟨remaining, deficit⟩ hremaining hcatch).2
    by_cases hlow : deficit < a
    · refine ⟨a + 1, by simp [remaining], ?_⟩
      rw [hmoveFirst]
      simp only [pairFormulaExact]
      split_ifs <;> (try simp [Outcome.neg]) <;> omega
    · by_cases hmiddle : deficit ≤ a + 1
      · refine ⟨a + 3, by simp [remaining], ?_⟩
        rw [hmoveThird]
        simp only [pairFormulaExact]
        split_ifs <;> (try simp [Outcome.neg]) <;> omega
      · refine ⟨a + 2, by simp [remaining], ?_⟩
        rw [hmoveSecond]
        simp only [pairFormulaExact]
        split_ifs <;> (try simp [Outcome.neg]) <;> omega

def tripleWithoutSecondFormula (a deficit : ℕ) : Outcome :=
  if deficit = a + 1 then .draw else if deficit = a + 2 then .loss else .win

/-- Exact value after deleting the second of four consecutive counters. -/
theorem value_triple_without_second (a deficit : ℕ) (ha : 5 ≤ a)
    (hdeficit : deficit ≤ a + 3) :
    Position.value ⟨{a, a + 2, a + 3}, deficit⟩ = tripleWithoutSecondFormula a deficit := by
  let remaining : Finset ℕ := {a, a + 2, a + 3}
  have hremaining : remaining ≠ ∅ := by simp [remaining]
  have hcatch : ¬remaining.sum (fun counter => counter) < deficit := by
    simp [remaining]
    omega
  have heraseFirst : remaining.erase a = {a + 2, a + 3} := by
    ext counter
    simp [remaining]
  have heraseSecond : remaining.erase (a + 2) = {a, a + 3} := by
    ext counter
    simp [remaining]
    omega
  have heraseThird : remaining.erase (a + 3) = {a, a + 2} := by
    ext counter
    simp [remaining]
    omega
  have hmoveFirst := move_outcome_eq_pair_formula_exact remaining a (a + 2) (a + 3)
    deficit heraseFirst (by omega) (by omega) (by omega)
  have hmoveSecond := move_outcome_eq_pair_formula_exact remaining (a + 2) a (a + 3)
    deficit heraseSecond (by omega) (by omega) (by omega)
  have hmoveThird := move_outcome_eq_pair_formula_exact remaining (a + 3) a (a + 2)
    deficit heraseThird (by omega) (by omega) (by omega)
  unfold tripleWithoutSecondFormula
  by_cases hdraw : deficit = a + 1
  · rw [ite_eq_left hdraw]
    subst deficit
    have hfirstDraw :
        (⟨remaining, a + 1⟩ : Position).moveOutcome a = .draw := by
      rw [hmoveFirst]
      simp [pairFormulaExact]
    have hsecondLoss :
        (⟨remaining, a + 1⟩ : Position).moveOutcome (a + 2) = .loss := by
      rw [hmoveSecond]
      simp [pairFormulaExact, Outcome.neg]
    have hthirdDraw :
        (⟨remaining, a + 1⟩ : Position).moveOutcome (a + 3) = .draw := by
      rw [hmoveThird]
      simp [pairFormulaExact, Outcome.neg]
    apply (value_eq_draw_iff ⟨remaining, a + 1⟩ hremaining hcatch).2
    constructor
    · exact ⟨a, by simp [remaining], by simp [hfirstDraw]⟩
    · intro counter hcounter
      simp only [remaining, Finset.mem_insert, Finset.mem_singleton] at hcounter
      rcases hcounter with hcounter | hcounter | hcounter
      · subst counter
        simp [hfirstDraw]
      · subst counter
        simp [hsecondLoss]
      · subst counter
        simp [hthirdDraw]
  · rw [ite_eq_right hdraw]
    by_cases hloss : deficit = a + 2
    · rw [ite_eq_left hloss]
      subst deficit
      have hfirstLoss :
          (⟨remaining, a + 2⟩ : Position).moveOutcome a = .loss := by
        rw [hmoveFirst]
        simp [pairFormulaExact]
      have hsecondLoss :
          (⟨remaining, a + 2⟩ : Position).moveOutcome (a + 2) = .loss := by
        rw [hmoveSecond]
        simp [pairFormulaExact, Outcome.neg]
      have hthirdLoss :
          (⟨remaining, a + 2⟩ : Position).moveOutcome (a + 3) = .loss := by
        rw [hmoveThird]
        simp [pairFormulaExact, Outcome.neg]
      apply (value_eq_loss_iff ⟨remaining, a + 2⟩ hremaining hcatch).2
      intro counter hcounter
      simp only [remaining, Finset.mem_insert, Finset.mem_singleton] at hcounter
      rcases hcounter with hcounter | hcounter | hcounter
      · subst counter
        exact hfirstLoss
      · subst counter
        exact hsecondLoss
      · subst counter
        exact hthirdLoss
    · rw [ite_eq_right hloss]
      apply (value_eq_win_iff ⟨remaining, deficit⟩ hremaining hcatch).2
      by_cases hlow : deficit + 2 ≤ a
      · refine ⟨a, by simp [remaining], ?_⟩
        rw [hmoveFirst]
        simp only [pairFormulaExact]
        split_ifs <;> (try simp [Outcome.neg]) <;> omega
      · by_cases hmiddle : deficit ≤ a
        · refine ⟨a + 3, by simp [remaining], ?_⟩
          rw [hmoveThird]
          simp only [pairFormulaExact]
          split_ifs <;> (try simp [Outcome.neg]) <;> omega
        · refine ⟨a + 2, by simp [remaining], ?_⟩
          rw [hmoveSecond]
          simp only [pairFormulaExact]
          split_ifs <;> (try simp [Outcome.neg]) <;> omega

/-- Deleting the third of four consecutive counters always leaves a winning position. -/
theorem value_triple_without_third (a deficit : ℕ) (ha : 5 ≤ a)
    (hdeficit : deficit ≤ a + 3) :
    Position.value ⟨{a, a + 1, a + 3}, deficit⟩ = .win := by
  let remaining : Finset ℕ := {a, a + 1, a + 3}
  have hremaining : remaining ≠ ∅ := by simp [remaining]
  have hcatch : ¬remaining.sum (fun counter => counter) < deficit := by
    simp [remaining]
    omega
  have heraseFirst : remaining.erase a = {a + 1, a + 3} := by
    ext counter
    simp [remaining]
  have heraseSecond : remaining.erase (a + 1) = {a, a + 3} := by
    ext counter
    simp [remaining]
    omega
  have heraseThird : remaining.erase (a + 3) = {a, a + 1} := by
    ext counter
    simp [remaining]
    omega
  have hmoveFirst := move_outcome_eq_pair_formula_exact remaining a (a + 1) (a + 3)
    deficit heraseFirst (by omega) (by omega) (by omega)
  have hmoveSecond := move_outcome_eq_pair_formula_exact remaining (a + 1) a (a + 3)
    deficit heraseSecond (by omega) (by omega) (by omega)
  have hmoveThird := move_outcome_eq_pair_formula_exact remaining (a + 3) a (a + 1)
    deficit heraseThird (by omega) (by omega) (by omega)
  apply (value_eq_win_iff ⟨remaining, deficit⟩ hremaining hcatch).2
  by_cases hlow : deficit + 3 ≤ a
  · refine ⟨a, by simp [remaining], ?_⟩
    rw [hmoveFirst]
    simp only [pairFormulaExact]
    split_ifs <;> (try simp [Outcome.neg]) <;> omega
  · by_cases hmiddle : deficit ≤ a
    · refine ⟨a + 3, by simp [remaining], ?_⟩
      rw [hmoveThird]
      simp only [pairFormulaExact]
      split_ifs <;> (try simp [Outcome.neg]) <;> omega
    · by_cases hnext : deficit = a + 1
      · refine ⟨a, by simp [remaining], ?_⟩
        rw [hmoveFirst]
        simp only [pairFormulaExact]
        split_ifs <;> (try simp [Outcome.neg]) <;> omega
      · refine ⟨a + 1, by simp [remaining], ?_⟩
        rw [hmoveSecond]
        simp only [pairFormulaExact]
        split_ifs <;> (try simp [Outcome.neg]) <;> omega

def tripleWithoutFourthFormula (a deficit : ℕ) : Outcome :=
  if deficit = a + 1 then .draw else if deficit = a + 3 then .draw else .win

/-- Exact value after deleting the fourth of four consecutive counters. -/
theorem value_triple_without_fourth (a deficit : ℕ) (ha : 5 ≤ a)
    (hdeficit : deficit ≤ a + 3) :
    Position.value ⟨{a, a + 1, a + 2}, deficit⟩ = tripleWithoutFourthFormula a deficit := by
  let remaining : Finset ℕ := {a, a + 1, a + 2}
  have hremaining : remaining ≠ ∅ := by simp [remaining]
  have hcatch : ¬remaining.sum (fun counter => counter) < deficit := by
    simp [remaining]
    omega
  have heraseFirst : remaining.erase a = {a + 1, a + 2} := by
    ext counter
    simp [remaining]
  have heraseSecond : remaining.erase (a + 1) = {a, a + 2} := by
    ext counter
    simp [remaining]
    omega
  have heraseThird : remaining.erase (a + 2) = {a, a + 1} := by
    ext counter
    simp [remaining]
    omega
  have hmoveFirst := move_outcome_eq_pair_formula_exact remaining a (a + 1) (a + 2)
    deficit heraseFirst (by omega) (by omega) (by omega)
  have hmoveSecond := move_outcome_eq_pair_formula_exact remaining (a + 1) a (a + 2)
    deficit heraseSecond (by omega) (by omega) (by omega)
  have hmoveThird := move_outcome_eq_pair_formula_exact remaining (a + 2) a (a + 1)
    deficit heraseThird (by omega) (by omega) (by omega)
  unfold tripleWithoutFourthFormula
  by_cases hfirstDraw : deficit = a + 1
  · rw [ite_eq_left hfirstDraw]
    subst deficit
    have hfirstMoveDraw :
        (⟨remaining, a + 1⟩ : Position).moveOutcome a = .draw := by
      rw [hmoveFirst]
      simp [pairFormulaExact]
    have hsecondMoveLoss :
        (⟨remaining, a + 1⟩ : Position).moveOutcome (a + 1) = .loss := by
      rw [hmoveSecond]
      simp [pairFormulaExact, Outcome.neg]
    have hthirdMoveDraw :
        (⟨remaining, a + 1⟩ : Position).moveOutcome (a + 2) = .draw := by
      rw [hmoveThird]
      simp [pairFormulaExact, Outcome.neg]
    apply (value_eq_draw_iff ⟨remaining, a + 1⟩ hremaining hcatch).2
    constructor
    · exact ⟨a, by simp [remaining], by simp [hfirstMoveDraw]⟩
    · intro counter hcounter
      simp only [remaining, Finset.mem_insert, Finset.mem_singleton] at hcounter
      rcases hcounter with hcounter | hcounter | hcounter
      · subst counter
        simp [hfirstMoveDraw]
      · subst counter
        simp [hsecondMoveLoss]
      · subst counter
        simp [hthirdMoveDraw]
  · rw [ite_eq_right hfirstDraw]
    by_cases hsecondDraw : deficit = a + 3
    · rw [ite_eq_left hsecondDraw]
      subst deficit
      have hfirstMoveLoss :
          (⟨remaining, a + 3⟩ : Position).moveOutcome a = .loss := by
        rw [hmoveFirst]
        simp [pairFormulaExact]
        omega
      have hsecondMoveDraw :
          (⟨remaining, a + 3⟩ : Position).moveOutcome (a + 1) = .draw := by
        rw [hmoveSecond]
        simp [pairFormulaExact]
      have hthirdMoveDraw :
          (⟨remaining, a + 3⟩ : Position).moveOutcome (a + 2) = .draw := by
        rw [hmoveThird]
        simp [pairFormulaExact]
      apply (value_eq_draw_iff ⟨remaining, a + 3⟩ hremaining hcatch).2
      constructor
      · exact ⟨a + 1, by simp [remaining], by simp [hsecondMoveDraw]⟩
      · intro counter hcounter
        simp only [remaining, Finset.mem_insert, Finset.mem_singleton] at hcounter
        rcases hcounter with hcounter | hcounter | hcounter
        · subst counter
          simp [hfirstMoveLoss]
        · subst counter
          simp [hsecondMoveDraw]
        · subst counter
          simp [hthirdMoveDraw]
    · rw [ite_eq_right hsecondDraw]
      apply (value_eq_win_iff ⟨remaining, deficit⟩ hremaining hcatch).2
      by_cases hlow : deficit + 2 ≤ a
      · refine ⟨a, by simp [remaining], ?_⟩
        rw [hmoveFirst]
        simp only [pairFormulaExact]
        split_ifs <;> (try simp [Outcome.neg]) <;> omega
      · by_cases hmiddle : deficit ≤ a
        · refine ⟨a + 2, by simp [remaining], ?_⟩
          rw [hmoveThird]
          simp only [pairFormulaExact]
          split_ifs <;> (try simp [Outcome.neg]) <;> omega
        · refine ⟨a + 1, by simp [remaining], ?_⟩
          rw [hmoveSecond]
          simp only [pairFormulaExact]
          split_ifs <;> (try simp [Outcome.neg]) <;> omega

/-- The exact outcome profile for four consecutive counters beginning at `a`. -/
def topFourFormula (a deficit : ℕ) : Outcome :=
  if deficit = 0 then .draw
  else if deficit = 2 then .draw
  else if deficit ≤ a then .loss
  else .win

/-- Exact normalized value of four consecutive counters at every relevant deficit. -/
theorem value_top_four (a deficit : ℕ) (ha : 5 ≤ a) (hdeficit : deficit ≤ a + 3) :
    Position.value ⟨{a, a + 1, a + 2, a + 3}, deficit⟩ = topFourFormula a deficit := by
  let remaining : Finset ℕ := {a, a + 1, a + 2, a + 3}
  have hremaining : remaining ≠ ∅ := by simp [remaining]
  have hcatch : ¬remaining.sum (fun counter => counter) < deficit := by
    simp [remaining]
    omega
  have heraseFirst : remaining.erase a = {a + 1, a + 2, a + 3} := by
    ext counter
    simp [remaining]
  have heraseSecond : remaining.erase (a + 1) = {a, a + 2, a + 3} := by
    ext counter
    simp [remaining]
    omega
  have heraseThird : remaining.erase (a + 2) = {a, a + 1, a + 3} := by
    ext counter
    simp [remaining]
    omega
  have heraseFourth : remaining.erase (a + 3) = {a, a + 1, a + 2} := by
    ext counter
    simp [remaining]
    omega
  have hmoveFirst :
      (⟨remaining, deficit⟩ : Position).moveOutcome a =
        if a < deficit then tripleWithoutFirstFormula a (deficit - a)
        else (tripleWithoutFirstFormula a (a - deficit)).neg := by
    by_cases hcontinue : a < deficit
    · rw [ite_eq_left hcontinue]
      simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_true]
      rw [heraseFirst, value_triple_without_first a (deficit - a) ha (by omega)]
    · rw [ite_eq_right hcontinue]
      simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_false]
      rw [heraseFirst, value_triple_without_first a (a - deficit) ha (by omega)]
  have hmoveSecond :
      (⟨remaining, deficit⟩ : Position).moveOutcome (a + 1) =
        if a + 1 < deficit then tripleWithoutSecondFormula a (deficit - (a + 1))
        else (tripleWithoutSecondFormula a (a + 1 - deficit)).neg := by
    by_cases hcontinue : a + 1 < deficit
    · rw [ite_eq_left hcontinue]
      simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_true]
      rw [heraseSecond, value_triple_without_second a (deficit - (a + 1)) ha (by omega)]
    · rw [ite_eq_right hcontinue]
      simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_false]
      rw [heraseSecond, value_triple_without_second a (a + 1 - deficit) ha (by omega)]
  have hmoveThird :
      (⟨remaining, deficit⟩ : Position).moveOutcome (a + 2) =
        if a + 2 < deficit then .win else .loss := by
    by_cases hcontinue : a + 2 < deficit
    · rw [ite_eq_left hcontinue]
      simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_true]
      rw [heraseThird, value_triple_without_third a (deficit - (a + 2)) ha (by omega)]
    · rw [ite_eq_right hcontinue]
      simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_false]
      rw [heraseThird, value_triple_without_third a (a + 2 - deficit) ha (by omega)]
      rfl
  have hmoveFourth :
      (⟨remaining, deficit⟩ : Position).moveOutcome (a + 3) =
        if a + 3 < deficit then tripleWithoutFourthFormula a (deficit - (a + 3))
        else (tripleWithoutFourthFormula a (a + 3 - deficit)).neg := by
    by_cases hcontinue : a + 3 < deficit
    · rw [ite_eq_left hcontinue]
      simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_true]
      rw [heraseFourth, value_triple_without_fourth a (deficit - (a + 3)) ha (by omega)]
    · rw [ite_eq_right hcontinue]
      simp only [Position.moveOutcome, Position.afterPick, hcontinue, ite_false]
      rw [heraseFourth, value_triple_without_fourth a (a + 3 - deficit) ha (by omega)]
  unfold topFourFormula
  by_cases hzero : deficit = 0
  · rw [ite_eq_left hzero]
    subst deficit
    have hfirstLoss : (⟨remaining, 0⟩ : Position).moveOutcome a = .loss := by
      rw [hmoveFirst]
      simp [tripleWithoutFirstFormula, Outcome.neg]
    have hsecondDraw : (⟨remaining, 0⟩ : Position).moveOutcome (a + 1) = .draw := by
      rw [hmoveSecond]
      simp [tripleWithoutSecondFormula, Outcome.neg]
    have hthirdLoss : (⟨remaining, 0⟩ : Position).moveOutcome (a + 2) = .loss := by
      rw [hmoveThird]
      simp
    have hfourthDraw : (⟨remaining, 0⟩ : Position).moveOutcome (a + 3) = .draw := by
      rw [hmoveFourth]
      simp [tripleWithoutFourthFormula, Outcome.neg]
    apply (value_eq_draw_iff ⟨remaining, 0⟩ hremaining hcatch).2
    constructor
    · exact ⟨a + 1, by simp [remaining], by simp [hsecondDraw]⟩
    · intro counter hcounter
      simp only [remaining, Finset.mem_insert, Finset.mem_singleton] at hcounter
      rcases hcounter with hcounter | hcounter | hcounter | hcounter
      · subst counter
        simp [hfirstLoss]
      · subst counter
        simp [hsecondDraw]
      · subst counter
        simp [hthirdLoss]
      · subst counter
        simp [hfourthDraw]
  · rw [ite_eq_right hzero]
    by_cases htwo : deficit = 2
    · rw [ite_eq_left htwo]
      subst deficit
      have hfirstLoss : (⟨remaining, 2⟩ : Position).moveOutcome a = .loss := by
        rw [hmoveFirst]
        simp only [tripleWithoutFirstFormula]
        split_ifs <;> (try simp [Outcome.neg]) <;> omega
      have hsecondLoss : (⟨remaining, 2⟩ : Position).moveOutcome (a + 1) = .loss := by
        rw [hmoveSecond]
        simp only [tripleWithoutSecondFormula]
        split_ifs <;> (try simp [Outcome.neg]) <;> omega
      have hthirdLoss : (⟨remaining, 2⟩ : Position).moveOutcome (a + 2) = .loss := by
        rw [hmoveThird]
        simp
      have hfourthDraw : (⟨remaining, 2⟩ : Position).moveOutcome (a + 3) = .draw := by
        rw [hmoveFourth]
        simp [tripleWithoutFourthFormula, Outcome.neg]
      apply (value_eq_draw_iff ⟨remaining, 2⟩ hremaining hcatch).2
      constructor
      · exact ⟨a + 3, by simp [remaining], by simp [hfourthDraw]⟩
      · intro counter hcounter
        simp only [remaining, Finset.mem_insert, Finset.mem_singleton] at hcounter
        rcases hcounter with hcounter | hcounter | hcounter | hcounter
        · subst counter
          simp [hfirstLoss]
        · subst counter
          simp [hsecondLoss]
        · subst counter
          simp [hthirdLoss]
        · subst counter
          simp [hfourthDraw]
    · rw [ite_eq_right htwo]
      by_cases hloss : deficit ≤ a
      · rw [ite_eq_left hloss]
        have hfirstLoss : (⟨remaining, deficit⟩ : Position).moveOutcome a = .loss := by
          rw [hmoveFirst]
          simp only [tripleWithoutFirstFormula]
          split_ifs <;> (try simp [Outcome.neg]) <;> omega
        have hsecondLoss :
            (⟨remaining, deficit⟩ : Position).moveOutcome (a + 1) = .loss := by
          rw [hmoveSecond]
          simp only [tripleWithoutSecondFormula]
          split_ifs <;> (try simp [Outcome.neg]) <;> omega
        have hthirdLoss : (⟨remaining, deficit⟩ : Position).moveOutcome (a + 2) = .loss := by
          rw [hmoveThird]
          simp
          omega
        have hfourthLoss :
            (⟨remaining, deficit⟩ : Position).moveOutcome (a + 3) = .loss := by
          rw [hmoveFourth]
          simp only [tripleWithoutFourthFormula]
          split_ifs <;> (try simp [Outcome.neg]) <;> omega
        apply (value_eq_loss_iff ⟨remaining, deficit⟩ hremaining hcatch).2
        intro counter hcounter
        simp only [remaining, Finset.mem_insert, Finset.mem_singleton] at hcounter
        rcases hcounter with hcounter | hcounter | hcounter | hcounter
        · subst counter
          exact hfirstLoss
        · subst counter
          exact hsecondLoss
        · subst counter
          exact hthirdLoss
        · subst counter
          exact hfourthLoss
      · rw [ite_eq_right hloss]
        apply (value_eq_win_iff ⟨remaining, deficit⟩ hremaining hcatch).2
        refine ⟨a, by simp [remaining], ?_⟩
        rw [hmoveFirst]
        simp only [tripleWithoutFirstFormula]
        split_ifs <;> (try simp [Outcome.neg]) <;> omega

/-- Four consecutive counters whose least element is at least `5` form a losing position at
deficit `4`, despite their bottom and top pairs exactly matching the two draw quotas. -/
theorem value_top_four_deficit_four (a : ℕ) (ha : 5 ≤ a) :
    Position.value ⟨{a, a + 1, a + 2, a + 3}, 4⟩ = .loss := by
  rw [value_top_four a 4 ha (by omega)]
  simp [topFourFormula]
  omega

/-- Symbolically classify any ordered subset of four consecutive counters. -/
def topSubsetValue? (a deficit : ℕ) : List ℕ → Option Outcome
  | [] => some (if deficit = 0 then .draw else .loss)
  | [x] =>
      if a ≤ x ∧ x ≤ a + 3 then
        some (if deficit < x then .win else if deficit = x then .draw else .loss)
      else none
  | [x, y] =>
      if a ≤ x ∧ x < y ∧ y ≤ a + 3 then some (pairFormulaExact x y deficit) else none
  | [x, y, z] =>
      if x = a + 1 ∧ y = a + 2 ∧ z = a + 3 then
        some (tripleWithoutFirstFormula a deficit)
      else if x = a ∧ y = a + 2 ∧ z = a + 3 then
        some (tripleWithoutSecondFormula a deficit)
      else if x = a ∧ y = a + 1 ∧ z = a + 3 then
        some .win
      else if x = a ∧ y = a + 1 ∧ z = a + 2 then
        some (tripleWithoutFourthFormula a deficit)
      else none
  | [x, y, z, w] =>
      if x = a ∧ y = a + 1 ∧ z = a + 2 ∧ w = a + 3 then
        some (topFourFormula a deficit)
      else none
  | _ => none

/-- Every outcome returned by `topSubsetValue?` is the exact normalized game value. -/
theorem top_subset_value?_sound (a deficit : ℕ) (counters : List ℕ) (outcome : Outcome)
    (ha : 5 ≤ a) (hdeficit : deficit ≤ a + 3)
    (hvalue : topSubsetValue? a deficit counters = some outcome) :
    Position.value ⟨counters.toFinset, deficit⟩ = outcome := by
  cases counters with
  | nil =>
      have houtcome : (if deficit = 0 then .draw else .loss) = outcome := by
        simpa [topSubsetValue?] using hvalue
      rw [← houtcome]
      simpa using value_empty deficit
  | cons x counters =>
      cases counters with
      | nil =>
          by_cases hguard : a ≤ x ∧ x ≤ a + 3
          · have houtcome :
                (if deficit < x then .win else if deficit = x then .draw else .loss) = outcome := by
              simpa [topSubsetValue?, hguard] using hvalue
            rw [← houtcome]
            simpa using value_singleton x deficit
          · simp [topSubsetValue?, hguard] at hvalue
      | cons y counters =>
          cases counters with
          | nil =>
              by_cases hguard : a ≤ x ∧ x < y ∧ y ≤ a + 3
              · have houtcome : pairFormulaExact x y deficit = outcome := by
                  simpa [topSubsetValue?, hguard] using hvalue
                rw [← houtcome]
                simpa using earlier_value_pair_exact x y deficit (by omega) hguard.2.1 (by omega)
              · simp [topSubsetValue?, hguard] at hvalue
          | cons z counters =>
              cases counters with
              | nil =>
                  by_cases hfirst : x = a + 1 ∧ y = a + 2 ∧ z = a + 3
                  · rcases hfirst with ⟨rfl, rfl, rfl⟩
                    have houtcome : tripleWithoutFirstFormula a deficit = outcome := by
                      simpa [topSubsetValue?] using hvalue
                    rw [← houtcome]
                    simpa using value_triple_without_first a deficit ha hdeficit
                  · by_cases hsecond : x = a ∧ y = a + 2 ∧ z = a + 3
                    · rcases hsecond with ⟨hx, hy, hz⟩
                      subst x
                      subst y
                      subst z
                      have houtcome : tripleWithoutSecondFormula a deficit = outcome := by
                        simpa [topSubsetValue?, hfirst] using hvalue
                      rw [← houtcome]
                      simpa using value_triple_without_second a deficit ha hdeficit
                    · by_cases hthird : x = a ∧ y = a + 1 ∧ z = a + 3
                      · rcases hthird with ⟨hx, hy, hz⟩
                        subst x
                        subst y
                        subst z
                        have houtcome : .win = outcome := by
                          simpa [topSubsetValue?, hfirst, hsecond] using hvalue
                        rw [← houtcome]
                        simpa using value_triple_without_third a deficit ha hdeficit
                      · by_cases hfourth : x = a ∧ y = a + 1 ∧ z = a + 2
                        · rcases hfourth with ⟨hx, hy, hz⟩
                          subst x
                          subst y
                          subst z
                          have houtcome : tripleWithoutFourthFormula a deficit = outcome := by
                            simpa [topSubsetValue?, hfirst, hsecond, hthird] using hvalue
                          rw [← houtcome]
                          simpa using value_triple_without_fourth a deficit ha hdeficit
                        · simp [topSubsetValue?, hfirst, hsecond, hthird, hfourth] at hvalue
              | cons w counters =>
                  cases counters with
                  | nil =>
                      by_cases hfull : x = a ∧ y = a + 1 ∧ z = a + 2 ∧ w = a + 3
                      · rcases hfull with ⟨hx, hy, hz, hw⟩
                        subst x
                        subst y
                        subst z
                        subst w
                        have houtcome : topFourFormula a deficit = outcome := by
                          simpa [topSubsetValue?] using hvalue
                        rw [← houtcome]
                        simpa using value_top_four a deficit ha hdeficit
                      · simp [topSubsetValue?, hfull] at hvalue
                  | cons fifth counters =>
                      simp [topSubsetValue?] at hvalue

end CatchUpSearch.TopFourClassification
