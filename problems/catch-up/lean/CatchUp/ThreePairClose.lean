/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ThreePairClose.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates.
-/
module

public import Mathlib
public import CatchUp.DeficitTwo

/-! Symbolic paired endgames. All parameters are unbounded natural numbers. -/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.TiedFour

theorem pair_nonloss_iff (a b d : ℕ) (ha : 0 < a)
    (hab : a < b) (hg : b-a ≤ a) :
    Position.value ⟨{a,b},d⟩ ≠ .loss ↔
      d ≤ b-a ∨ (a < d ∧ d ≤ a+b) := by
  rw [CatchUpSearch.TopFourClassification.value_pair_exact a b d ha hab hg]
  unfold CatchUpSearch.TopFourClassification.pairFormulaExact
  split_ifs <;> simp_all <;> omega

theorem pair_nonwin_iff (a b d : ℕ) (ha : 0 < a)
    (hab : a < b) (hg : b-a ≤ a) :
    Position.value ⟨{a,b},d⟩ ≠ .win ↔
      (b-a ≤ d ∧ d ≤ a) ∨ a+b ≤ d := by
  rw [CatchUpSearch.TopFourClassification.value_pair_exact a b d ha hab hg]
  unfold CatchUpSearch.TopFourClassification.pairFormulaExact
  split_ifs <;> simp_all
  omega

private theorem nonloss_step (R : Finset ℕ) (d : ℕ)
    (he : R ≠ ∅) (hc : d ≤ R.sum id) :
    Position.value ⟨R,d⟩ ≠ .loss ↔ ∃ x ∈ R,
      (x < d ∧ Position.value ⟨R.erase x,d-x⟩ ≠ .loss) ∨
      (d ≤ x ∧ Position.value ⟨R.erase x,x-d⟩ ≠ .win) := by
  have hstep : Position.value ⟨R,d⟩ ≠ .loss ↔
      ∃ x ∈ R, (⟨R,d⟩ : Position).moveOutcome x ≠ .loss := by
    rw [Position.value_eq_best_move_outcome _ he (Nat.not_lt.mpr hc),
      Outcome.best_ne_loss_iff]
    simp
  rw [hstep]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  by_cases h : x < d <;>
    simp [Position.moveOutcome, Position.afterPick, h,
      show d ≤ x ↔ ¬ x < d by omega]

theorem nonwin_step (R : Finset ℕ) (d : ℕ)
    (he : R ≠ ∅) (hc : d ≤ R.sum id) :
    Position.value ⟨R,d⟩ ≠ .win ↔ ∀ x ∈ R,
      (x < d → Position.value ⟨R.erase x,d-x⟩ ≠ .win) ∧
      (d ≤ x → Position.value ⟨R.erase x,x-d⟩ ≠ .loss) := by
  have hstep : Position.value ⟨R,d⟩ ≠ .win ↔
      ∀ x ∈ R, (⟨R,d⟩ : Position).moveOutcome x ≠ .win := by
    rw [Position.value_eq_best_move_outcome _ he (Nat.not_lt.mpr hc),
      Outcome.best_ne_win_iff]
    simp
  rw [hstep]
  apply forall_congr'
  intro x
  apply imp_congr_right
  intro hx
  by_cases h : x < d <;>
    simp [Position.moveOutcome, Position.afterPick, h,
      show d ≤ x ↔ ¬ x < d by omega]



/-- Exact non-loss ranges for three counters lying below twice the minimum. -/
theorem three_close_nonloss_iff (a b c d : ℕ) (ha : 0 < a)
    (hab : a < b) (hbc : b < c) (hc : c < 2*a) (hd : d < 2*a) :
    Position.value ⟨{a,b,c},d⟩ ≠ .loss ↔
      d ≤ a+b-c ∨ (c-a ≤ d ∧ d ≤ a+c-b) ∨ (b < d ∧ d ≤ b+c-a) := by
  have hs : d ≤ ({a,b,c} : Finset ℕ).sum id := by
    simp [show a ≠ b by omega, show a ≠ c by omega, show b ≠ c by omega]
    omega
  have ea : ({a,b,c} : Finset ℕ).erase a = {b,c} := by ext t; simp; omega
  have eb : ({a,b,c} : Finset ℕ).erase b = {a,c} := by ext t; simp; omega
  have ec : ({a,b,c} : Finset ℕ).erase c = {a,b} := by ext t; simp; omega
  rw [nonloss_step _ _ (by simp) hs]
  simp only [Finset.exists_mem_insert, Finset.mem_singleton, exists_eq_left]
  simp only [ea, eb, ec,
    pair_nonloss_iff b c _ (by omega) hbc (by omega),
    pair_nonwin_iff b c _ (by omega) hbc (by omega),
    pair_nonloss_iff a c _ ha (by omega) (by omega),
    pair_nonwin_iff a c _ ha (by omega) (by omega),
    pair_nonloss_iff a b _ ha hab (by omega),
    pair_nonwin_iff a b _ ha hab (by omega)]
  omega

/-- The strict-win ranges have the same lower endpoints, with strict upper bounds. -/
theorem three_close_nonwin_iff (a b c d : ℕ) (ha : 0 < a)
    (hab : a < b) (hbc : b < c) (hc : c < 2*a) (hd : d < 2*a) :
    Position.value ⟨{a,b,c},d⟩ ≠ .win ↔
      ¬ (d < a+b-c ∨ (c-a ≤ d ∧ d < a+c-b) ∨ (b < d ∧ d < b+c-a)) := by
  have hs : d ≤ ({a,b,c} : Finset ℕ).sum id := by
    simp [show a ≠ b by omega, show a ≠ c by omega, show b ≠ c by omega]
    omega
  have ea : ({a,b,c} : Finset ℕ).erase a = {b,c} := by ext t; simp; omega
  have eb : ({a,b,c} : Finset ℕ).erase b = {a,c} := by ext t; simp; omega
  have ec : ({a,b,c} : Finset ℕ).erase c = {a,b} := by ext t; simp; omega
  rw [nonwin_step _ _ (by simp) hs]
  simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
  simp only [ea, eb, ec,
    pair_nonloss_iff b c _ (by omega) hbc (by omega),
    pair_nonwin_iff b c _ (by omega) hbc (by omega),
    pair_nonloss_iff a c _ ha (by omega) (by omega),
    pair_nonwin_iff a c _ ha (by omega) (by omega),
    pair_nonloss_iff a b _ ha hab (by omega),
    pair_nonwin_iff a b _ ha hab (by omega)]
  omega



private theorem four_nonloss_step (a b c e d : ℕ)
    (hab : a < b) (hbc : b < c) (hce : c < e) (hd : d < 2*a) :
    Position.value ⟨{a,b,c,e},d⟩ ≠ .loss ↔
      (a < d ∧ Position.value ⟨{b,c,e},d-a⟩ ≠ .loss ∨
        d ≤ a ∧ Position.value ⟨{b,c,e},a-d⟩ ≠ .win) ∨
      (b < d ∧ Position.value ⟨{a,c,e},d-b⟩ ≠ .loss ∨
        d ≤ b ∧ Position.value ⟨{a,c,e},b-d⟩ ≠ .win) ∨
      (c < d ∧ Position.value ⟨{a,b,e},d-c⟩ ≠ .loss ∨
        d ≤ c ∧ Position.value ⟨{a,b,e},c-d⟩ ≠ .win) ∨
      (e < d ∧ Position.value ⟨{a,b,c},d-e⟩ ≠ .loss ∨
        d ≤ e ∧ Position.value ⟨{a,b,c},e-d⟩ ≠ .win) := by
  have hs : d ≤ ({a,b,c,e} : Finset ℕ).sum id := by
    simp [show a ≠ b by omega, show a ≠ c by omega, show a ≠ e by omega,
      show b ≠ c by omega, show b ≠ e by omega, show c ≠ e by omega]
    omega
  have ea : ({a,b,c,e} : Finset ℕ).erase a = {b,c,e} := by ext t; simp; omega
  have eb : ({a,b,c,e} : Finset ℕ).erase b = {a,c,e} := by ext t; simp; omega
  have ec : ({a,b,c,e} : Finset ℕ).erase c = {a,b,e} := by ext t; simp; omega
  have ee : ({a,b,c,e} : Finset ℕ).erase e = {a,b,c} := by ext t; simp; omega
  rw [nonloss_step _ _ (by simp) hs]
  simp only [Finset.exists_mem_insert, Finset.mem_singleton, exists_eq_left, ea, eb, ec, ee]

private theorem four_nonwin_step (a b c e d : ℕ)
    (hab : a < b) (hbc : b < c) (hce : c < e) (hd : d < 2*a) :
    Position.value ⟨{a,b,c,e},d⟩ ≠ .win ↔
      ((a < d → Position.value ⟨{b,c,e},d-a⟩ ≠ .win) ∧
        (d ≤ a → Position.value ⟨{b,c,e},a-d⟩ ≠ .loss)) ∧
      ((b < d → Position.value ⟨{a,c,e},d-b⟩ ≠ .win) ∧
        (d ≤ b → Position.value ⟨{a,c,e},b-d⟩ ≠ .loss)) ∧
      ((c < d → Position.value ⟨{a,b,e},d-c⟩ ≠ .win) ∧
        (d ≤ c → Position.value ⟨{a,b,e},c-d⟩ ≠ .loss)) ∧
      ((e < d → Position.value ⟨{a,b,c},d-e⟩ ≠ .win) ∧
        (d ≤ e → Position.value ⟨{a,b,c},e-d⟩ ≠ .loss)) := by
  have hs : d ≤ ({a,b,c,e} : Finset ℕ).sum id := by
    simp [show a ≠ b by omega, show a ≠ c by omega, show a ≠ e by omega,
      show b ≠ c by omega, show b ≠ e by omega, show c ≠ e by omega]
    omega
  have ea : ({a,b,c,e} : Finset ℕ).erase a = {b,c,e} := by ext t; simp; omega
  have eb : ({a,b,c,e} : Finset ℕ).erase b = {a,c,e} := by ext t; simp; omega
  have ec : ({a,b,c,e} : Finset ℕ).erase c = {a,b,e} := by ext t; simp; omega
  have ee : ({a,b,c,e} : Finset ℕ).erase e = {a,b,c} := by ext t; simp; omega
  rw [nonwin_step _ _ (by simp) hs]
  simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq, ea, eb, ec, ee]



set_option maxHeartbeats 1600000 in
/-- The dense case: at least one upper-counter opening avoids loss.
The proof retains all five opposing replies and all four possible replies to them. -/
theorem three_pairs_close_nonloss (a b c : ℕ) (ha : 3 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hc : c+1 < 2*a) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},1⟩ ≠ .loss := by
  have er0 : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (a+1) = {a,b,b+1,c,c+1} := by ext t; simp; omega
  have er1 : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,a+1,b,c,c+1} := by ext t; simp; omega
  have er2 : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,c} := by ext t; simp; omega
  suffices hm : Position.value ⟨{a,b,b+1,c,c+1},a⟩ ≠ .win ∨
      Position.value ⟨{a,a+1,b,c,c+1},b⟩ ≠ .win ∨
      Position.value ⟨{a,a+1,b,b+1,c},c⟩ ≠ .win by
    rcases hm with hm | hm | hm
    · apply (nonloss_step _ _ (by simp) (by
        exact (show 1 ≤ a+1 by omega).trans
          (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (show a+1 ∈ ({a,a+1,b,b+1,c,c+1} : Finset ℕ) by simp)))).mpr
      exact ⟨a+1,by simp,Or.inr ⟨by omega,by simpa only [er0,show a+1-1=a by omega] using hm⟩⟩
    · apply (nonloss_step _ _ (by simp) (by
        exact (show 1 ≤ b+1 by omega).trans
          (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (show b+1 ∈ ({a,a+1,b,b+1,c,c+1} : Finset ℕ) by simp)))).mpr
      exact ⟨b+1,by simp,Or.inr ⟨by omega,by simpa only [er1,show b+1-1=b by omega] using hm⟩⟩
    · apply (nonloss_step _ _ (by simp) (by
        exact (show 1 ≤ c+1 by omega).trans
          (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (show c+1 ∈ ({a,a+1,b,b+1,c,c+1} : Finset ℕ) by simp)))).mpr
      exact ⟨c+1,by simp,Or.inr ⟨by omega,by simpa only [er2,show c+1-1=c by omega] using hm⟩⟩
  have e00 : ({a,b,b+1,c,c+1} : Finset ℕ).erase (a) = {b,b+1,c,c+1} := by ext t; simp; omega
  have e01 : ({a,b,b+1,c,c+1} : Finset ℕ).erase (b) = {a,b+1,c,c+1} := by ext t; simp; omega
  have e02 : ({a,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,b,c,c+1} := by ext t; simp; omega
  have e03 : ({a,b,b+1,c,c+1} : Finset ℕ).erase (c) = {a,b,b+1,c+1} := by ext t; simp; omega
  have e04 : ({a,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {a,b,b+1,c} := by ext t; simp; omega
  have e10 : ({a,a+1,b,c,c+1} : Finset ℕ).erase (a) = {a+1,b,c,c+1} := by ext t; simp; omega
  have e11 : ({a,a+1,b,c,c+1} : Finset ℕ).erase (a+1) = {a,b,c,c+1} := by ext t; simp; omega
  have e12 : ({a,a+1,b,c,c+1} : Finset ℕ).erase (b) = {a,a+1,c,c+1} := by ext t; simp; omega
  have e13 : ({a,a+1,b,c,c+1} : Finset ℕ).erase (c) = {a,a+1,b,c+1} := by ext t; simp; omega
  have e14 : ({a,a+1,b,c,c+1} : Finset ℕ).erase (c+1) = {a,a+1,b,c} := by ext t; simp; omega
  have e20 : ({a,a+1,b,b+1,c} : Finset ℕ).erase (a) = {a+1,b,b+1,c} := by ext t; simp; omega
  have e21 : ({a,a+1,b,b+1,c} : Finset ℕ).erase (a+1) = {a,b,b+1,c} := by ext t; simp; omega
  have e22 : ({a,a+1,b,b+1,c} : Finset ℕ).erase (b) = {a,a+1,b+1,c} := by ext t; simp; omega
  have e23 : ({a,a+1,b,b+1,c} : Finset ℕ).erase (b+1) = {a,a+1,b,c} := by ext t; simp; omega
  have e24 : ({a,a+1,b,b+1,c} : Finset ℕ).erase (c) = {a,a+1,b,b+1} := by ext t; simp; omega
  rw [nonwin_step {a,b,b+1,c,c+1} a (by simp) (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (show a ∈ ({a,b,b+1,c,c+1} : Finset ℕ) by simp))]
  rw [nonwin_step {a,a+1,b,c,c+1} b (by simp) (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (show b ∈ ({a,a+1,b,c,c+1} : Finset ℕ) by simp))]
  rw [nonwin_step {a,a+1,b,b+1,c} c (by simp) (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (show c ∈ ({a,a+1,b,b+1,c} : Finset ℕ) by simp))]
  simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq,
    e00,e01,e02,e03,e04,e10,e11,e12,e13,e14,e20,e21,e22,e23,e24]
  simp (disch := omega) only [four_nonloss_step, four_nonwin_step]
  simp (disch := omega) only [three_close_nonloss_iff, three_close_nonwin_iff]
  omega

end CatchUp.TiedFour
