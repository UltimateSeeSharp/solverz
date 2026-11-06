/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/CanonicalSmall.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.FiveThree

/-! Canonical even-start pairs. The minimum-six classification isolates the
boundary anchor four, with no upper bound on magnitudes or gaps. -/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.CanonicalSmall

open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (nonloss_of_continue)
open CatchUp.DeficitTwo (all_catching)
open CatchUp.DeficitTwo (adjacent_pair_loss)

/-- Only starts `(6,10)` and `(6,12)` are excluded at deficit six. -/
theorem two_six_nonwin (a b : ℕ) (ha : 6 ≤ a) (hab : a+2 ≤ b)
    (hae : a%2=0) (hbe : b%2=0)
    (hex : ¬ (a=6 ∧ (b=10 ∨ b=12))) :
    Position.value ⟨{a,a+1,b,b+1},6⟩ ≠ .win := by
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase a = {a+1,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
    have hf : ({a+1,b,b+1} : Finset ℕ).erase (a+1) = {b,b+1} := by ext t; simp; omega
    rw [hf,show a+1-(a-6)=7 by omega,adjacent_pair_loss b 7 (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase (a+1) = {a,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ a (by simp) (by omega)
    have hf : ({a,b,b+1} : Finset ℕ).erase a = {b,b+1} := by ext t; simp; omega
    rw [hf,show a-(a+1-6)=5 by omega,adjacent_pair_loss b 5 (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase b = {a,a+1,b+1} := by ext t; simp; omega
    rw [he]
    by_cases ha8 : 8 ≤ a
    · apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({a,a+1,b+1} : Finset ℕ).erase (b+1) = {a,a+1} := by ext t; simp; omega
      rw [hf,show b+1-(b-6)=7 by omega,adjacent_pair_loss a 7 (by omega) (by omega)]
      decide
    · have ha6 : a=6 := by omega
      subst a
      by_cases hb8 : b=8
      · subst b
        rw [← Position.eval_eq_value]
        decide +kernel
      · have hb14 : 14 ≤ b := by omega
        have hs : b+1 ≤ ({6,6+1,b+1} : Finset ℕ).sum id :=
          Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
        apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
        have hf : ({6,6+1,b+1} : Finset ℕ).erase 6 = {7,b+1} := by ext t; simp; omega
        rw [hf,show b-6-6=b-12 by omega]
        apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
        have hg : ({7,b+1} : Finset ℕ).erase (b+1) = {7} := by ext t; simp; omega
        rw [hg,show b+1-(b-12)=13 by omega,← Position.eval_eq_value]
        decide +kernel
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase (b+1) = {a,a+1,b} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({a,a+1,b} : Finset ℕ).erase b = {a,a+1} := by ext t; simp; omega
    rw [hf,show b-(b+1-6)=5 by omega,adjacent_pair_loss a 5 (by omega) (by omega)]
    decide



private theorem ten_repair (c : ℕ) (hc : 12 ≤ c) (hce : c%2=0)
    (hex : c≠12 ∧ c≠20) :
    Position.value ⟨{6,7,10,11,c+1},c-5⟩ ≠ .loss := by
  by_cases hc22 : 22 ≤ c
  · have he : ({6,7,10,11,c+1} : Finset ℕ).erase 6 = {7,10,11,c+1} := by ext t; simp; omega
    have hf : ({7,10,11,c+1} : Finset ℕ).erase 10 = {7,11,c+1} := by ext t; simp; omega
    have hg : ({7,11,c+1} : Finset ℕ).erase (c+1) = {7,11} := by ext t; simp; omega
    have hs : c+1 ≤ ({6,7,10,11,c+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
    rw [he,show c-5-6=c-11 by omega]
    have ht : c+1 ≤ ({7,10,11,c+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 10 (by simp) (by omega) (by omega)
    rw [hf,show c-11-10=c-21 by omega]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    rw [hg,show c+1-(c-21)=22 by omega,← Position.eval_eq_value]
    decide +kernel
  · have hcases : c=14 ∨ c=16 ∨ c=18 := by omega
    rcases hcases with rfl | rfl | rfl <;> rw [← Position.eval_eq_value] <;> decide +kernel

private theorem twelve_repair (c : ℕ) (hc : 14 ≤ c) :
    Position.value ⟨{6,7,12,13,c+1},c-5⟩ ≠ .loss := by
  have he : ({6,7,12,13,c+1} : Finset ℕ).erase 6 = {7,12,13,c+1} := by ext t; simp; omega
  have hf : ({7,12,13,c+1} : Finset ℕ).erase (c+1) = {7,12,13} := by ext t; simp; omega
  have hs : c+1 ≤ ({6,7,12,13,c+1} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
  apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
  rw [he,show c-5-6=c-11 by omega]
  apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
  rw [hf,show c+1-(c-11)=12 by omega,← Position.eval_eq_value]
  decide +kernel

/-- The only canonical three-pair wins at deficit five and minimum six
have starts `(6,10,12)` or `(6,10,20)`. -/
theorem three_five_nonwin (a b c : ℕ) (ha : 6 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c)
    (hae : a%2=0) (hbe : b%2=0) (hce : c%2=0)
    (hex : ¬ (a=6 ∧ b=10 ∧ (c=12 ∨ c=20))) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},5⟩ ≠ .win := by
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (a) = {a+1,b,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
    have hf : ({a+1,b,b+1,c,c+1} : Finset ℕ).erase (a+1) = {b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show (a+1)-((a)-5)=6 by omega]
    exact two_six_nonwin b c (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (a+1) = {a,b,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (a) (by simp) (by omega)
    have hf : ({a,b,b+1,c,c+1} : Finset ℕ).erase (a) = {b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show (a)-((a+1)-5)=4 by omega]
    exact DeficitTwo.two_pairs_four_nonwin b c (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (b) = {a,a+1,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    by_cases hsmall : a=6 ∧ (c=10 ∨ c=12)
    · obtain ⟨rfl,hsmall⟩ := hsmall
      have hb8 : b=8 := by omega
      subst b
      rcases hsmall with rfl | rfl <;> rw [← Position.eval_eq_value] <;> decide +kernel
    · apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({a,a+1,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,a+1,c,c+1} := by ext t; simp; omega
      rw [hf,show (b+1)-((b)-5)=6 by omega]
      exact two_six_nonwin a c (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,a+1,b,c,c+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b) (by simp) (by omega)
    have hf : ({a,a+1,b,c,c+1} : Finset ℕ).erase (b) = {a,a+1,c,c+1} := by ext t; simp; omega
    rw [hf,show (b)-((b+1)-5)=4 by omega]
    exact DeficitTwo.two_pairs_four_nonwin a c (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (c) = {a,a+1,b,b+1,c+1} := by ext t; simp; omega
    rw [he]
    by_cases hb10 : a=6 ∧ b=10
    · obtain ⟨rfl,rfl⟩ := hb10
      exact ten_repair c (by omega) hce (by omega)
    by_cases hb12 : a=6 ∧ b=12
    · obtain ⟨rfl,rfl⟩ := hb12
      exact twelve_repair c (by omega)
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1} := by ext t; simp; omega
    rw [hf,show (c+1)-((c)-5)=6 by omega]
    exact two_six_nonwin a b (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,c} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (c) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c} : Finset ℕ).erase (c) = {a,a+1,b,b+1} := by ext t; simp; omega
    rw [hf,show (c)-((c+1)-5)=4 by omega]
    exact DeficitTwo.two_pairs_four_nonwin a b (by omega) (by omega) (by omega)



/-- Exact strict-win classification, not merely a list of exclusions. -/
theorem two_six_win_iff (a b : ℕ) (ha : 6 ≤ a) (hab : a+2 ≤ b)
    (hae : a%2=0) (hbe : b%2=0) :
    Position.value ⟨{a,a+1,b,b+1},6⟩ = .win ↔ a=6 ∧ (b=10 ∨ b=12) := by
  constructor
  · intro hw
    by_contra hex
    exact two_six_nonwin a b ha hab hae hbe hex hw
  · rintro ⟨rfl,hb⟩
    rcases hb with rfl | rfl <;> rw [← Position.eval_eq_value] <;> decide +kernel

/-- Exact strict-win classification for the three-pair reserve. -/
theorem three_five_win_iff (a b c : ℕ) (ha : 6 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c)
    (hae : a%2=0) (hbe : b%2=0) (hce : c%2=0) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},5⟩ = .win ↔ a=6 ∧ b=10 ∧ (c=12 ∨ c=20) := by
  constructor
  · intro hw
    by_contra hex
    exact three_five_nonwin a b c ha hab hbc hae hbe hce hex hw
  · rintro ⟨rfl,rfl,hc⟩
    rcases hc with rfl | rfl <;> rw [← Position.eval_eq_value] <;> decide +kernel

theorem nonloss_iff_check (p : Position) : p.value ≠ .loss ↔
    CatchUpSearch.CanAvoidLossClassifier.check .p1 ⟨p,.p1⟩ = true := by
  rw [CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff,can_avoid_loss_iff_value]
  simp

theorem nonwin_iff_check (p : Position) : p.value ≠ .win ↔
    CatchUpSearch.CanAvoidLossClassifier.check .p2 ⟨p,.p1⟩ = true := by
  rw [CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff,can_avoid_loss_iff_value]
  simp

end CatchUp.CanonicalSmall
