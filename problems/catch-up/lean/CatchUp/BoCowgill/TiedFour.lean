/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/TiedFour.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.ThreePairClose

/-!
# TiedFour

Tied four-pair and deficit-one five-pair nonwinning results under explicit separation assumptions.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.TiedFour

open CatchUp.AdjacentPairRepair
open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (all_catching)
open CatchUp.DeficitTwo (nonloss_of_continue)
open CatchUp.AdjacentPairRepair (pair_low_deficit_nonloss)
open CatchUp.TiedFour (pair_nonloss_iff)
open CatchUp.TiedFour (pair_nonwin_iff)

private theorem boundary_three_nonwin (a b c : ℕ) (ha : 0 < a)
    (hab : a < b) (hbc : b < c) (hb : b < 2*a)
    (hc : c ≤ a+b) (hs : 2*a+b < 2*c) :
    Position.value ⟨{a,b,c},a+b-c⟩ ≠ .win := by
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx <;> subst x
  · have he : ({a,b,c} : Finset ℕ).erase a = {b,c} := by ext t; simp; omega
    rw [he]
    apply pair_low_deficit_nonloss _ _ _ (by omega) (by omega)
  · have he : ({a,b,c} : Finset ℕ).erase b = {a,c} := by ext t; simp; omega
    rw [he]
    apply pair_low_deficit_nonloss _ _ _ (by omega) (by omega)
  · have he : ({a,b,c} : Finset ℕ).erase c = {a,b} := by ext t; simp; omega
    rw [he]
    exact (pair_nonloss_iff a b _ ha hab (by omega)).mpr (Or.inr ⟨by omega,by omega⟩)

/-- The smallest upper counter is safe whenever the last pair is sufficiently high. -/
theorem three_pairs_wide_nonloss (a b c : ℕ)
    (ha : 2 ≤ a) (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hsep : 2*a-1 ≤ c) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},1⟩ ≠ .loss := by
  by_cases hb : 2*a-1 ≤ b
  · exact three_pairs_nonloss_of_separation a b c ha hab hbc hb
  apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
  have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (a+1) =
      {a,b,b+1,c,c+1} := by
    ext t
    simp
    omega
  rw [he, show a+1-1=a by omega]
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase a = {b,b+1,c,c+1} := by
      ext t
      simp
      omega
    rw [he, Nat.sub_self, position_value_zero_deficit_eq_value,
      two_pairs_tied_draw b c (by omega) hbc]
    decide
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase (b) = {a,b+1,c,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({a,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,c,c+1} := by
      ext t
      simp
      omega
    rw [hf, show (b+1)-((b)-a)=a+1 by omega, orphan_plus_draw a c ha (by omega)]
    decide
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,b,c,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (b) (by simp) (by omega)
    have hf : ({a,b,c,c+1} : Finset ℕ).erase (b) = {a,c,c+1} := by
      ext t
      simp
      omega
    rw [hf, show (b)-((b+1)-a)=a-1 by omega, orphan_minus_draw a c ha (by omega) (by omega)]
    decide
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase (c) = {a,b,b+1,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    have hf : ({a,b,b+1,c+1} : Finset ℕ).erase (c+1) = {a,b,b+1} := by
      ext t
      simp
      omega
    rw [hf, show (c+1)-((c)-a)=a+1 by omega, orphan_plus_draw a b ha hab]
    decide
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {a,b,b+1,c} := by
      ext t; simp; omega
    rw [he]
    by_cases hbcSum : c ≤ a+b
    · apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({a,b,b+1,c} : Finset ℕ).erase (b+1) = {a,b,c} := by
        ext t; simp; omega
      rw [hf,show b+1-(c+1-a)=a+b-c by omega]
      exact boundary_three_nonwin a b c (by omega) (by omega) (by omega)
        (by omega) hbcSum (by omega)
    · have hsum : c ≤ ({a,b,b+1,c} : Finset ℕ).sum id :=
        Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
      apply nonloss_of_continue _ _ (b+1) (by simp) (by omega) (by omega)
      have hf : ({a,b,b+1,c} : Finset ℕ).erase (b+1) = {a,b,c} := by
        ext t; simp; omega
      rw [hf,show c+1-a-(b+1)=c-a-b by omega]
      apply nonloss_of_catch _ _ c (by simp) (by omega)
      have hg : ({a,b,c} : Finset ℕ).erase c = {a,b} := by ext t; simp; omega
      rw [hg,show c-(c-a-b)=a+b by omega]
      exact (pair_nonwin_iff a b (a+b) (by omega) (by omega) (by omega)).mpr (Or.inr (by omega))



/-- Three arbitrary disjoint adjacent pairs draw at deficit one, from minimum three. -/
theorem three_pairs_one_draw (a b c : ℕ) (ha : 3 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},1⟩ = .draw := by
  apply (Outcome.eq_draw_iff _).mpr
  constructor
  · by_cases hc : 2*a-1 ≤ c
    · exact three_pairs_wide_nonloss a b c (by omega) hab hbc hc
    · exact three_pairs_close_nonloss a b c ha hab hbc (by omega)
  · exact three_pairs_nonwin a b c ha hab hbc

/-- Every opening has a legal mate reply. Upper picks require a continued turn. -/
theorem four_pairs_tied_nonwin (a b c e : ℕ) (ha : 3 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1},0⟩ ≠ .win := by
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a) = {a+1,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he,Nat.sub_zero]
    apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
    have hf : ({a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a+1) = {b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show (a+1)-(a)=1 by omega,three_pairs_one_draw b c e (by omega) (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a+1) = {a,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he,Nat.sub_zero]
    have hf : ({a,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a) = {b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    have hs : 1 ≤ ({b,b+1,c,c+1,e,e+1} : Finset ℕ).sum id :=
      (show 1 ≤ b by omega).trans
        (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp))
    have ht : (({a,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a)).sum id + (a) = ({a,b,b+1,c,c+1,e,e+1} : Finset ℕ).sum id :=
      Finset.sum_erase_add _ id (show a ∈ ({a,b,b+1,c,c+1,e,e+1} : Finset ℕ) by simp)
    rw [hf] at ht
    apply nonloss_of_continue _ _ (a) (by simp) (by omega) (by omega)
    rw [hf,show a+1-(a)=1 by omega,three_pairs_one_draw b c e (by omega) (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b) = {a,a+1,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he,Nat.sub_zero]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({a,a+1,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b+1) = {a,a+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show (b+1)-(b)=1 by omega,three_pairs_one_draw a c e (by omega) (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b+1) = {a,a+1,b,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he,Nat.sub_zero]
    have hf : ({a,a+1,b,c,c+1,e,e+1} : Finset ℕ).erase (b) = {a,a+1,c,c+1,e,e+1} := by ext t; simp; omega
    have hs : 1 ≤ ({a,a+1,c,c+1,e,e+1} : Finset ℕ).sum id :=
      (show 1 ≤ a by omega).trans
        (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp))
    have ht : (({a,a+1,b,c,c+1,e,e+1} : Finset ℕ).erase (b)).sum id + (b) = ({a,a+1,b,c,c+1,e,e+1} : Finset ℕ).sum id :=
      Finset.sum_erase_add _ id (show b ∈ ({a,a+1,b,c,c+1,e,e+1} : Finset ℕ) by simp)
    rw [hf] at ht
    apply nonloss_of_continue _ _ (b) (by simp) (by omega) (by omega)
    rw [hf,show b+1-(b)=1 by omega,three_pairs_one_draw a c e (by omega) (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (c) = {a,a+1,b,b+1,c+1,e,e+1} := by ext t; simp; omega
    rw [he,Nat.sub_zero]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c+1,e,e+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,e,e+1} := by ext t; simp; omega
    rw [hf,show (c+1)-(c)=1 by omega,three_pairs_one_draw a b e (by omega) (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,c,e,e+1} := by ext t; simp; omega
    rw [he,Nat.sub_zero]
    have hf : ({a,a+1,b,b+1,c,e,e+1} : Finset ℕ).erase (c) = {a,a+1,b,b+1,e,e+1} := by ext t; simp; omega
    have hs : 1 ≤ ({a,a+1,b,b+1,e,e+1} : Finset ℕ).sum id :=
      (show 1 ≤ a by omega).trans
        (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp))
    have ht : (({a,a+1,b,b+1,c,e,e+1} : Finset ℕ).erase (c)).sum id + (c) = ({a,a+1,b,b+1,c,e,e+1} : Finset ℕ).sum id :=
      Finset.sum_erase_add _ id (show c ∈ ({a,a+1,b,b+1,c,e,e+1} : Finset ℕ) by simp)
    rw [hf] at ht
    apply nonloss_of_continue _ _ (c) (by simp) (by omega) (by omega)
    rw [hf,show c+1-(c)=1 by omega,three_pairs_one_draw a b e (by omega) (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (e) = {a,a+1,b,b+1,c,c+1,e+1} := by ext t; simp; omega
    rw [he,Nat.sub_zero]
    apply nonloss_of_catch _ _ (e+1) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,c+1,e+1} : Finset ℕ).erase (e+1) = {a,a+1,b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show (e+1)-(e)=1 by omega,three_pairs_one_draw a b c (by omega) (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (e+1) = {a,a+1,b,b+1,c,c+1,e} := by ext t; simp; omega
    rw [he,Nat.sub_zero]
    have hf : ({a,a+1,b,b+1,c,c+1,e} : Finset ℕ).erase (e) = {a,a+1,b,b+1,c,c+1} := by ext t; simp; omega
    have hs : 1 ≤ ({a,a+1,b,b+1,c,c+1} : Finset ℕ).sum id :=
      (show 1 ≤ a by omega).trans
        (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp))
    have ht : (({a,a+1,b,b+1,c,c+1,e} : Finset ℕ).erase (e)).sum id + (e) = ({a,a+1,b,b+1,c,c+1,e} : Finset ℕ).sum id :=
      Finset.sum_erase_add _ id (show e ∈ ({a,a+1,b,b+1,c,c+1,e} : Finset ℕ) by simp)
    rw [hf] at ht
    apply nonloss_of_continue _ _ (e) (by simp) (by omega) (by omega)
    rw [hf,show e+1-(e)=1 by omega,three_pairs_one_draw a b c (by omega) (by omega) (by omega)]
    decide
/-- Uniform deficit-one five-pair theorem, with arbitrary pair gaps. -/
theorem five_pairs_one_nonwin (a b c e f : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1,f,f+1},1⟩ ≠ .win := by
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (a) = {a+1,b,b+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
    have hf : ({a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (a+1) = {b,b+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [hf,show (a+1)-(a-1)=2 by omega]
    exact CatchUp.DeficitTwo.four_pairs_two_nonwin b c e f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (a+1) = {a,b,b+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (a) (by simp) (by omega)
    have hf : ({a,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (a) = {b,b+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [hf,show (a)-(a+1-1)=0 by omega]
    exact four_pairs_tied_nonwin b c e f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (b) = {a,a+1,b+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({a,a+1,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (b+1) = {a,a+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [hf,show (b+1)-(b-1)=2 by omega]
    exact CatchUp.DeficitTwo.four_pairs_two_nonwin a c e f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (b+1) = {a,a+1,b,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b) (by simp) (by omega)
    have hf : ({a,a+1,b,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (b) = {a,a+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [hf,show (b)-(b+1-1)=0 by omega]
    exact four_pairs_tied_nonwin a c e f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (c) = {a,a+1,b,b+1,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c+1,e,e+1,f,f+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [hf,show (c+1)-(c-1)=2 by omega]
    exact CatchUp.DeficitTwo.four_pairs_two_nonwin a b e f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,c,e,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (c) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,e,e+1,f,f+1} : Finset ℕ).erase (c) = {a,a+1,b,b+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [hf,show (c)-(c+1-1)=0 by omega]
    exact four_pairs_tied_nonwin a b e f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (e) = {a,a+1,b,b+1,c,c+1,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (e+1) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,c+1,e+1,f,f+1} : Finset ℕ).erase (e+1) = {a,a+1,b,b+1,c,c+1,f,f+1} := by ext t; simp; omega
    rw [hf,show (e+1)-(e-1)=2 by omega]
    exact CatchUp.DeficitTwo.four_pairs_two_nonwin a b c f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (e+1) = {a,a+1,b,b+1,c,c+1,e,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (e) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,c+1,e,f,f+1} : Finset ℕ).erase (e) = {a,a+1,b,b+1,c,c+1,f,f+1} := by ext t; simp; omega
    rw [hf,show (e)-(e+1-1)=0 by omega]
    exact four_pairs_tied_nonwin a b c f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (f) = {a,a+1,b,b+1,c,c+1,e,e+1,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (f+1) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,c+1,e,e+1,f+1} : Finset ℕ).erase (f+1) = {a,a+1,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show (f+1)-(f-1)=2 by omega]
    exact CatchUp.DeficitTwo.four_pairs_two_nonwin a b c e (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (f+1) = {a,a+1,b,b+1,c,c+1,e,e+1,f} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (f) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,c+1,e,e+1,f} : Finset ℕ).erase (f) = {a,a+1,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show (f)-(f+1-1)=0 by omega]
    exact four_pairs_tied_nonwin a b c e (by omega) (by omega) (by omega) (by omega)

end CatchUp.TiedFour
