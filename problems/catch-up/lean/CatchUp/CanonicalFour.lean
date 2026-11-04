/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/CanonicalFour.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.CanonicalSmall

/-!
# CanonicalFour

Classifies canonical four-pair deficit-four positions, including the exceptional winning geometry
(6,10,20,40).
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.CanonicalFour

open CatchUp.CanonicalSmall
open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (nonloss_of_continue)
open CatchUp.DeficitTwo (all_catching)
open CatchUp.CanonicalSmall (nonloss_iff_check)

private theorem repair_twelve (q : ℕ) (hq : 8 ≤ q) (hqe : q%2=0)
    (hgap : q=8 ∨ 14 ≤ q) :
    Position.value ⟨{6,7,10,11,12,13,q+1},q-4⟩ ≠ .loss := by
  by_cases hq22 : 22 ≤ q
  · have he : ({6,7,10,11,12,13,q+1} : Finset ℕ).erase 6 = {7,10,11,12,13,q+1} := by ext t; simp; omega
    have hf : ({7,10,11,12,13,q+1} : Finset ℕ).erase 10 = {7,11,12,13,q+1} := by ext t; simp; omega
    have hg : ({7,11,12,13,q+1} : Finset ℕ).erase (q+1) = {7,11,12,13} := by ext t; simp; omega
    have hs : q+1 ≤ ({6,7,10,11,12,13,q+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
    rw [he,show q-4-6=q-10 by omega]
    have ht : q+1 ≤ ({7,10,11,12,13,q+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 10 (by simp) (by omega) (by omega)
    rw [hf,show q-10-10=q-20 by omega]
    apply nonloss_of_catch _ _ (q+1) (by simp) (by omega)
    rw [hg,show q+1-(q-20)=21 by omega,← Position.eval_eq_value]
    decide +kernel
  · have hcases : q=8 ∨ q=14 ∨ q=16 ∨ q=18 ∨ q=20 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    all_goals rw [nonloss_iff_check]; decide +kernel

private theorem repair_twenty (q : ℕ) (hq : 8 ≤ q) (hqe : q%2=0)
    (hne : q≠10 ∧ q≠20 ∧ q≠40) :
    Position.value ⟨{6,7,10,11,20,21,q+1},q-4⟩ ≠ .loss := by
  by_cases hq42 : 42 ≤ q
  · have he : ({6,7,10,11,20,21,q+1} : Finset ℕ).erase 6 = {7,10,11,20,21,q+1} := by ext t; simp; omega
    have hf : ({7,10,11,20,21,q+1} : Finset ℕ).erase 10 = {7,11,20,21,q+1} := by ext t; simp; omega
    have hg : ({7,11,20,21,q+1} : Finset ℕ).erase 20 = {7,11,21,q+1} := by ext t; simp; omega
    have hh : ({7,11,21,q+1} : Finset ℕ).erase (q+1) = {7,11,21} := by ext t; simp; omega
    have hs : q+1 ≤ ({6,7,10,11,20,21,q+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
    rw [he,show q-4-6=q-10 by omega]
    have ht : q+1 ≤ ({7,10,11,20,21,q+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 10 (by simp) (by omega) (by omega)
    rw [hf,show q-10-10=q-20 by omega]
    have hu : q+1 ≤ ({7,11,20,21,q+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 20 (by simp) (by omega) (by omega)
    rw [hg,show q-20-20=q-40 by omega]
    apply nonloss_of_catch _ _ (q+1) (by simp) (by omega)
    rw [hh,show q+1-(q-40)=41 by omega,← Position.eval_eq_value]
    decide +kernel
  · have hcases : q=8 ∨ q=12 ∨ q=14 ∨ q=16 ∨ q=18 ∨ q=22 ∨ q=24 ∨
        q=26 ∨ q=28 ∨ q=30 ∨ q=32 ∨ q=34 ∨ q=36 ∨ q=38 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [nonloss_iff_check]; decide +kernel

private theorem orphan_nonloss (a b c q : ℕ) (ha : 6 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c)
    (hae : a%2=0) (hbe : b%2=0) (hce : c%2=0) (hq : 6 ≤ q) (hqe : q%2=0)
    (hqa : q+2 ≤ a ∨ a+2 ≤ q) (hqb : q+2 ≤ b ∨ b+2 ≤ q) (hqc : q+2 ≤ c ∨ c+2 ≤ q)
    (hex : ¬ (a=6 ∧ b=10 ∧ c=20 ∧ q=40)) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,q+1},q-4⟩ ≠ .loss := by
  by_cases h12 : a=6 ∧ b=10 ∧ c=12
  · obtain ⟨rfl,rfl,rfl⟩ := h12
    exact repair_twelve q (by omega) hqe (by omega)
  by_cases h20 : a=6 ∧ b=10 ∧ c=20
  · obtain ⟨rfl,rfl,rfl⟩ := h20
    exact repair_twenty q (by omega) hqe (by omega)
  apply nonloss_of_catch _ _ (q+1) (by simp) (by omega)
  have he : ({a,a+1,b,b+1,c,c+1,q+1} : Finset ℕ).erase (q+1) = {a,a+1,b,b+1,c,c+1} := by ext t; simp; omega
  rw [he,show q+1-(q-4)=5 by omega]
  exact three_five_nonwin a b c ha hab hbc hae hbe hce (by omega)



/-- All canonical four-pair deficit-four positions with minimum six are
nonwinning except the single geometry `(6,10,20,40)`. -/
theorem four_four_nonwin (a b c e : ℕ) (ha : 6 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e)
    (hae : a%2=0) (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0)
    (hex : ¬ (a=6 ∧ b=10 ∧ c=20 ∧ e=40)) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1},4⟩ ≠ .win := by
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a) = {a+1,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    have hf : ({a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ) = {b,b+1,c,c+1,e,e+1,a+1} := by ext t; simp only [Finset.mem_insert,Finset.mem_singleton]; omega
    rw [hf]
    exact orphan_nonloss b c e a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a+1) = {a,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ a (by simp) (by omega)
    have hf : ({a,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a) = {b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show a-(a+1-4)=3 by omega]
    exact DeficitTwo.three_pairs_three_nonwin b c e (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b) = {a,a+1,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    have hf : ({a,a+1,b+1,c,c+1,e,e+1} : Finset ℕ) = {a,a+1,c,c+1,e,e+1,b+1} := by ext t; simp only [Finset.mem_insert,Finset.mem_singleton]; omega
    rw [hf]
    exact orphan_nonloss a c e b (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b+1) = {a,a+1,b,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({a,a+1,b,c,c+1,e,e+1} : Finset ℕ).erase (b) = {a,a+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show b-(b+1-4)=3 by omega]
    exact DeficitTwo.three_pairs_three_nonwin a c e (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (c) = {a,a+1,b,b+1,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    have hf : ({a,a+1,b,b+1,c+1,e,e+1} : Finset ℕ) = {a,a+1,b,b+1,e,e+1,c+1} := by ext t; simp only [Finset.mem_insert,Finset.mem_singleton]; omega
    rw [hf]
    exact orphan_nonloss a b e c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,c,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ c (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,e,e+1} : Finset ℕ).erase (c) = {a,a+1,b,b+1,e,e+1} := by ext t; simp; omega
    rw [hf,show c-(c+1-4)=3 by omega]
    exact DeficitTwo.three_pairs_three_nonwin a b e (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (e) = {a,a+1,b,b+1,c,c+1,e+1} := by ext t; simp; omega
    rw [he]
    exact orphan_nonloss a b c e (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (e+1) = {a,a+1,b,b+1,c,c+1,e} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ e (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,c+1,e} : Finset ℕ).erase (e) = {a,a+1,b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show e-(e+1-4)=3 by omega]
    exact DeficitTwo.three_pairs_three_nonwin a b c (by omega) (by omega) (by omega) (by omega)

/-- The sparse exceptional quadruple really is a strict win. -/
theorem four_four_win_iff (a b c e : ℕ) (ha : 6 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e)
    (hae : a%2=0) (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1},4⟩ = .win ↔
      a=6 ∧ b=10 ∧ c=20 ∧ e=40 := by
  constructor
  · intro hw
    by_contra hex
    exact four_four_nonwin a b c e ha hab hbc hce hae hbe hcc hee hex hw
  · rintro ⟨rfl,rfl,rfl,rfl⟩
    rw [← Position.eval_eq_value]
    decide +kernel

end CatchUp.CanonicalFour
