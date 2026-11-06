/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/AnchorFour.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.AnchorFourEndgames

/-!
# AnchorFour

Four-pair and orphan defenses with the anchor {4,5}, subject to the stated excluded
counters/geometries.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.AnchorFour

open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (nonloss_of_continue)
open CatchUp.DeficitTwo (all_catching)
open CatchUp.CanonicalSmall (nonwin_iff_check)

private theorem orphan_three (b c q : ℕ) (hb : 6 ≤ b) (hbc : b+2 ≤ c)
    (hbe : b%2=0) (hce : c%2=0) (hbn : b≠8) (hcn : c≠8)
    (hq : 6 ≤ q) (hqe : q%2=0) (hqn : q≠8)
    (hqb : q+2 ≤ b ∨ b+2 ≤ q) (hqc : q+2 ≤ c ∨ c+2 ≤ q) :
    Position.value ⟨{4,5,b,b+1,c,c+1,q+1},q-4⟩ ≠ .loss := by
  by_cases hq6 : q=6
  · subst q
    apply nonloss_of_catch _ _ 4 (by simp) (by omega)
    have he : ({4,5,b,b+1,c,c+1,6+1} : Finset ℕ).erase 4 =
        {5,7,b,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    exact five_seven_two_pairs_two b c (by omega) hbc
  have hq10 : 10 ≤ q := by omega
  have hs : q+1 ≤ ({4,5,b,b+1,c,c+1,q+1} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
  apply nonloss_of_continue _ _ 4 (by simp) (by omega) (by omega)
  have he : ({4,5,b,b+1,c,c+1,q+1} : Finset ℕ).erase 4 =
      {5,b,b+1,c,c+1,q+1} := by ext t; simp; omega
  rw [he]
  apply nonloss_of_catch _ _ (q+1) (by simp) (by omega)
  have hf : ({5,b,b+1,c,c+1,q+1} : Finset ℕ).erase (q+1) =
      {5,b,b+1,c,c+1} := by ext t; simp; omega
  rw [hf,show q+1-(q-4-4)=9 by omega]
  exact five_two_pairs_nine b c hb hbc hbe hce hbn hcn

/-- An anchored-four four-pair win requires the pair starting at eight. -/
theorem four_four_nonwin_no_eight (b c e : ℕ) (hb : 6 ≤ b)
    (hbc : b+2 ≤ c) (hce : c+2 ≤ e)
    (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0)
    (hbn : b≠8) (hcn : c≠8) (hen : e≠8) :
    Position.value ⟨{4,5,b,b+1,c,c+1,e,e+1},4⟩ ≠ .win := by
  apply all_catching _ _ ⟨4,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({4,5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase 4 =
        {5,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    clear he
    by_cases hbad : b=6 ∧ c=10 ∧ (e=12 ∨ e=20)
    · obtain ⟨rfl,rfl,he⟩ := hbad
      rcases he with he | he
      · subst e
        apply nonloss_of_catch _ _ 10 (by decide +kernel) (by omega)
        have he : ({5,6,6+1,10,10+1,12,12+1} : Finset ℕ).erase 10 =
            {5,6,7,11,12,13} := by decide +kernel
        rw [he,nonwin_iff_check]
        decide +kernel
      · subst e
        apply nonloss_of_catch _ _ 20 (by decide +kernel) (by omega)
        have he : ({5,6,6+1,10,10+1,20,20+1} : Finset ℕ).erase 20 =
            {5,6,7,10,11,21} := by decide +kernel
        rw [he,nonwin_iff_check]
        decide +kernel
    apply nonloss_of_catch _ _ 5 (by simp) (by omega)
    have hf : ({5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase 5 =
        {b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf]
    exact CanonicalSmall.three_five_nonwin b c e hb hbc hce hbe hcc hee hbad
  · have he : ({4,5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase 5 =
        {4,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 4 (by simp) (by omega)
    have hf : ({4,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase 4 =
        {b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf]
    exact DeficitTwo.three_pairs_three_nonwin b c e (by omega) hbc hce (by omega)
  · have he : ({4,5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b) =
        {4,5,c,c+1,e,e+1,b+1} := by ext t; simp; omega
    rw [he]
    exact orphan_three c e b (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({4,5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b+1) =
        {4,5,c,c+1,e,e+1,b} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({4,5,c,c+1,e,e+1,b} : Finset ℕ).erase b =
        {4,5,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show b-(b+1-4)=3 by omega]
    exact DeficitTwo.three_pairs_three_nonwin 4 c e (by omega) (by omega) (by omega) (by omega)
  · have he : ({4,5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (c) =
        {4,5,b,b+1,e,e+1,c+1} := by ext t; simp; omega
    rw [he]
    exact orphan_three b e c (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({4,5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (c+1) =
        {4,5,b,b+1,e,e+1,c} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ c (by simp) (by omega)
    have hf : ({4,5,b,b+1,e,e+1,c} : Finset ℕ).erase c =
        {4,5,b,b+1,e,e+1} := by ext t; simp; omega
    rw [hf,show c-(c+1-4)=3 by omega]
    exact DeficitTwo.three_pairs_three_nonwin 4 b e (by omega) (by omega) (by omega) (by omega)
  · have he : ({4,5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (e) =
        {4,5,b,b+1,c,c+1,e+1} := by ext t; simp; omega
    rw [he]
    exact orphan_three b c e (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({4,5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (e+1) =
        {4,5,b,b+1,c,c+1,e} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ e (by simp) (by omega)
    have hf : ({4,5,b,b+1,c,c+1,e} : Finset ℕ).erase e =
        {4,5,b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show e-(e+1-4)=3 by omega]
    exact DeficitTwo.three_pairs_three_nonwin 4 b c (by omega) (by omega) (by omega) (by omega)

end CatchUp.AnchorFour
