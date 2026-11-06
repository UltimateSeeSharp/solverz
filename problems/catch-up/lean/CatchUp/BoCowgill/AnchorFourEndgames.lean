/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/AnchorFourEndgames.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.CanonicalFive
public import CatchUp.BoCowgill.TiedFour

/-!
# AnchorFourEndgames

Small endgames needed by defenses retaining the pair {4,5}.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.AnchorFour

open CatchUp.TiedFour (nonwin_step)
open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (nonloss_of_continue)
open CatchUp.DeficitTwo (all_catching)
open CatchUp.DeficitTwo (adjacent_pair_loss)
open CatchUp.AdjacentPairRepair (singleton_ge_nonwin)
open CatchUp.AdjacentPairRepair (adjacent_pair_draw)

/-- Excluding start eight suffices in the small anchor-five endgame. -/
theorem five_pair_ten_nonwin (b : ℕ) (hb : 6 ≤ b) (hbe : b%2=0) (hne : b≠8) :
    Position.value ⟨{5,b,b+1},10⟩ ≠ .win := by
  by_cases hb6 : b=6
  · subst b
    rw [← Position.eval_eq_value]
    decide +kernel
  have hb10 : 10 ≤ b := by omega
  have hs : 10 ≤ ({5,b,b+1} : Finset ℕ).sum id :=
    hb10.trans (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp))
  apply (nonwin_step _ _ (by simp) hs).mpr
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx <;> subst x
  · constructor
    · intro _
      have he : ({5,b,b+1} : Finset ℕ).erase 5 = {b,b+1} := by ext t; simp; omega
      rw [he,adjacent_pair_loss b 5 (by omega) (by omega)]
      decide
    · omega
  · constructor
    · omega
    · intro _
      have he : ({5,b,b+1} : Finset ℕ).erase b = {5,b+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({5,b+1} : Finset ℕ).erase (b+1) = {5} := by ext t; simp; omega
      rw [hf,show b+1-(b-10)=11 by omega]
      exact singleton_ge_nonwin 5 11 (by omega)
  · constructor
    · omega
    · intro _
      have he : ({5,b,b+1} : Finset ℕ).erase (b+1) = {5,b} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ b (by simp) (by omega)
      have hf : ({5,b} : Finset ℕ).erase b = {5} := by ext t; simp; omega
      rw [hf,show b-(b+1-10)=9 by omega]
      exact singleton_ge_nonwin 5 9 (by omega)

/-- At deficit eight the anchor-five endgame is uniformly nonwinning. -/
theorem five_pair_eight_nonwin (b : ℕ) (hb : 6 ≤ b) (hbe : b%2=0) :
    Position.value ⟨{5,b,b+1},8⟩ ≠ .win := by
  by_cases hb6 : b=6
  · subst b
    rw [← Position.eval_eq_value]
    decide +kernel
  have hb8 : 8 ≤ b := by omega
  have hs : 8 ≤ ({5,b,b+1} : Finset ℕ).sum id :=
    hb8.trans (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp))
  apply (nonwin_step _ _ (by simp) hs).mpr
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx <;> subst x
  · constructor
    · intro _
      have he : ({5,b,b+1} : Finset ℕ).erase 5 = {b,b+1} := by ext t; simp; omega
      rw [he,adjacent_pair_loss b 3 (by omega) (by omega)]
      decide
    · omega
  · constructor
    · omega
    · intro _
      have he : ({5,b,b+1} : Finset ℕ).erase b = {5,b+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({5,b+1} : Finset ℕ).erase (b+1) = {5} := by ext t; simp; omega
      rw [hf,show b+1-(b-8)=9 by omega]
      exact singleton_ge_nonwin 5 9 (by omega)
  · constructor
    · omega
    · intro _
      have he : ({5,b,b+1} : Finset ℕ).erase (b+1) = {5,b} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ b (by simp) (by omega)
      have hf : ({5,b} : Finset ℕ).erase b = {5} := by ext t; simp; omega
      rw [hf,show b-(b+1-8)=7 by omega]
      exact singleton_ge_nonwin 5 7 (by omega)

/-- The two fixed odd counters tolerate one higher canonical pair. -/
private theorem five_seven_pair_1 (b : ℕ) (hb : 8 ≤ b) :
    Position.value ⟨{5,7,b,b+1},1⟩ ≠ .win := by
  apply all_catching _ _ ⟨5,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  · have he : ({5,7,b,b+1} : Finset ℕ).erase 5 = {7,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 7 (by simp) (by omega)
    have hf : ({7,b,b+1} : Finset ℕ).erase 7 = {b,b+1} := by ext t; simp; omega
    rw [hf,show 7-(5-1)=3 by omega,adjacent_pair_loss b 3 (by omega) (by omega)]
    decide
  · have he : ({5,7,b,b+1} : Finset ℕ).erase 7 = {5,b,b+1} := by ext t; simp; omega
    rw [he]
    have hs : b+1 ≤ ({5,b,b+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 5 (by simp) (by omega) (by omega)
    have hf : ({5,b,b+1} : Finset ℕ).erase 5 = {b,b+1} := by ext t; simp; omega
    rw [hf,show 7-1-5=1 by omega,adjacent_pair_draw b (by omega)]
    decide
  · have he : ({5,7,b,b+1} : Finset ℕ).erase b = {5,7,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({5,7,b+1} : Finset ℕ).erase (b+1) = {5,7} := by ext t; simp; omega
    rw [hf,show b+1-(b-1)=2 by omega,← Position.eval_eq_value]
    decide +kernel
  · have he : ({5,7,b,b+1} : Finset ℕ).erase (b+1) = {5,7,b} := by ext t; simp; omega
    rw [he]
    have hs : b ≤ ({5,7,b} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 7 (by simp) (by omega) (by omega)
    have hf : ({5,7,b} : Finset ℕ).erase 7 = {5,b} := by ext t; simp; omega
    rw [hf]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hg : ({5,b} : Finset ℕ).erase b = {5} := by ext t; simp; omega
    rw [hg,show b-(b+1-1-7)=7 by omega]
    exact singleton_ge_nonwin 5 7 (by omega)

/-- The two fixed odd counters tolerate one higher canonical pair. -/
private theorem five_seven_pair_3 (b : ℕ) (hb : 8 ≤ b) :
    Position.value ⟨{5,7,b,b+1},3⟩ ≠ .win := by
  apply all_catching _ _ ⟨5,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  · have he : ({5,7,b,b+1} : Finset ℕ).erase 5 = {7,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 7 (by simp) (by omega)
    have hf : ({7,b,b+1} : Finset ℕ).erase 7 = {b,b+1} := by ext t; simp; omega
    rw [hf,show 7-(5-3)=5 by omega,adjacent_pair_loss b 5 (by omega) (by omega)]
    decide
  · have he : ({5,7,b,b+1} : Finset ℕ).erase 7 = {5,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 5 (by simp) (by omega)
    have hf : ({5,b,b+1} : Finset ℕ).erase 5 = {b,b+1} := by ext t; simp; omega
    rw [hf,show 5-(7-3)=1 by omega,adjacent_pair_draw b (by omega)]
    decide
  · have he : ({5,7,b,b+1} : Finset ℕ).erase b = {5,7,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({5,7,b+1} : Finset ℕ).erase (b+1) = {5,7} := by ext t; simp; omega
    rw [hf,show b+1-(b-3)=4 by omega,← Position.eval_eq_value]
    decide +kernel
  · have he : ({5,7,b,b+1} : Finset ℕ).erase (b+1) = {5,7,b} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({5,7,b} : Finset ℕ).erase b = {5,7} := by ext t; simp; omega
    rw [hf,show b-(b+1-3)=2 by omega,← Position.eval_eq_value]
    decide +kernel

/-- A continuing pick of six exposes these two odd counters at deficit two. -/
theorem five_seven_two_pairs_two (b c : ℕ) (hb : 10 ≤ b) (hbc : b+2 ≤ c) :
    Position.value ⟨{5,7,b,b+1,c,c+1},2⟩ ≠ .win := by
  apply all_catching _ _ ⟨5,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({5,7,b,b+1,c,c+1} : Finset ℕ).erase 5 = {7,b,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 7 (by simp) (by omega)
    have hf : ({7,b,b+1,c,c+1} : Finset ℕ).erase 7 = {b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show 7-(5-2)=4 by omega]
    exact DeficitTwo.two_pairs_four_nonwin b c (by omega) hbc (by omega)
  · have he : ({5,7,b,b+1,c,c+1} : Finset ℕ).erase 7 = {5,b,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 5 (by simp) (by omega)
    have hf : ({5,b,b+1,c,c+1} : Finset ℕ).erase 5 = {b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show 5-(7-2)=0 by omega,position_value_zero_deficit_eq_value,
      AdjacentPairRepair.two_pairs_tied_draw b c (by omega) hbc]
    decide
  · have he : ({5,7,b,b+1,c,c+1} : Finset ℕ).erase (b) = {5,7,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({5,7,b+1,c,c+1} : Finset ℕ).erase (b+1) = {5,7,c,c+1} := by ext t; simp; omega
    rw [hf,show (b+1)-((b)-2)=3 by omega]
    exact five_seven_pair_3 c (by omega)
  · have he : ({5,7,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {5,7,b,c,c+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b) (by simp) (by omega)
    have hf : ({5,7,b,c,c+1} : Finset ℕ).erase (b) = {5,7,c,c+1} := by ext t; simp; omega
    rw [hf,show (b)-((b+1)-2)=1 by omega]
    exact five_seven_pair_1 c (by omega)
  · have he : ({5,7,b,b+1,c,c+1} : Finset ℕ).erase (c) = {5,7,c+1,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    have hf : ({5,7,c+1,b,b+1} : Finset ℕ).erase (c+1) = {5,7,b,b+1} := by ext t; simp; omega
    rw [hf,show (c+1)-((c)-2)=3 by omega]
    exact five_seven_pair_3 b (by omega)
  · have he : ({5,7,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {5,7,c,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (c) (by simp) (by omega)
    have hf : ({5,7,c,b,b+1} : Finset ℕ).erase (c) = {5,7,b,b+1} := by ext t; simp; omega
    rw [hf,show (c)-((c+1)-2)=1 by omega]
    exact five_seven_pair_1 b (by omega)

/-- Two canonical pairs avoiding eight, beside five, are nonwinning at nine. -/
theorem five_two_pairs_nine (b c : ℕ) (hb : 6 ≤ b) (hbc : b+2 ≤ c)
    (hbe : b%2=0) (hce : c%2=0) (hbn : b≠8) (hcn : c≠8) :
    Position.value ⟨{5,b,b+1,c,c+1},9⟩ ≠ .win := by
  have hc10 : 10 ≤ c := by omega
  have hs : 9 ≤ ({5,b,b+1,c,c+1} : Finset ℕ).sum id :=
    (show 9 ≤ c by omega).trans
      (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp))
  apply (nonwin_step _ _ (by simp) hs).mpr
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> subst x
  · constructor
    · intro _
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase 5 = {b,b+1,c,c+1} := by ext t; simp; omega
      rw [he]
      exact DeficitTwo.two_pairs_four_nonwin b c (by omega) hbc (by omega)
    · omega
  · constructor
    · intro h
      have hb6 : b=6 := by omega
      subst b
      have he : ({5,6,6+1,c,c+1} : Finset ℕ).erase (6) = {5,7,c,c+1} := by ext t; simp; omega
      rw [he]
      exact five_seven_pair_3 c (by omega)
    · intro h
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase (b) = {5,b+1,c,c+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({5,b+1,c,c+1} : Finset ℕ).erase (b+1) = {5,c,c+1} := by ext t; simp; omega
      rw [hf,show (b+1)-((b)-9)=10 by omega]
      exact five_pair_ten_nonwin c (by omega) hce hcn
  · constructor
    · intro h
      have hb6 : b=6 := by omega
      subst b
      have he : ({5,6,6+1,c,c+1} : Finset ℕ).erase (6+1) = {5,6,c,c+1} := by ext t; simp; omega
      rw [he]
      exact AdjacentPairRepair.two_pairs_deficit_two_nonwin 5 c (by omega) (by omega)
    · intro h
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {5,b,c,c+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b) (by simp) (by omega)
      have hf : ({5,b,c,c+1} : Finset ℕ).erase (b) = {5,c,c+1} := by ext t; simp; omega
      rw [hf,show (b)-((b+1)-9)=8 by omega]
      exact five_pair_eight_nonwin c (by omega) hce
  · constructor
    · intro h
      omega
    · intro h
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase (c) = {5,c+1,b,b+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
      have hf : ({5,c+1,b,b+1} : Finset ℕ).erase (c+1) = {5,b,b+1} := by ext t; simp; omega
      rw [hf,show (c+1)-((c)-9)=10 by omega]
      exact five_pair_ten_nonwin b (by omega) hbe hbn
  · constructor
    · intro h
      omega
    · intro h
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {5,c,b,b+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (c) (by simp) (by omega)
      have hf : ({5,c,b,b+1} : Finset ℕ).erase (c) = {5,b,b+1} := by ext t; simp; omega
      rw [hf,show (c)-((c+1)-9)=8 by omega]
      exact five_pair_eight_nonwin b (by omega) hbe

private theorem five_pair_six_nonwin (b : ℕ) (hb : 6 ≤ b) (hbe : b%2=0) :
    Position.value ⟨{5,b,b+1},6⟩ ≠ .win := by
  by_cases hb6 : b=6
  · subst b
    rw [← Position.eval_eq_value]
    decide +kernel
  rw [AdjacentPairRepair.orphan_plus_draw 5 b (by omega) (by omega)]
  decide

/-- The companion deficit-seven family needs no exclusion at eight. -/
theorem five_two_pairs_seven (b c : ℕ) (hb : 6 ≤ b) (hbc : b+2 ≤ c)
    (hbe : b%2=0) (hce : c%2=0) :
    Position.value ⟨{5,b,b+1,c,c+1},7⟩ ≠ .win := by
  have hc8 : 8 ≤ c := by omega
  have hs : 7 ≤ ({5,b,b+1,c,c+1} : Finset ℕ).sum id :=
    (show 7 ≤ c by omega).trans
      (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp))
  apply (nonwin_step _ _ (by simp) hs).mpr
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> subst x
  · constructor
    · intro _
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase 5 = {b,b+1,c,c+1} := by ext t; simp; omega
      rw [he]
      exact AdjacentPairRepair.two_pairs_deficit_two_nonwin b c (by omega) hbc
    · omega
  · constructor
    · intro h
      have hb6 : b=6 := by omega
      subst b
      have he : ({5,6,6+1,c,c+1} : Finset ℕ).erase 6 = {5,7,c,c+1} := by ext t; simp; omega
      rw [he]
      exact five_seven_pair_1 c hc8
    · intro h
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase (b) = {5,b+1,c,c+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({5,b+1,c,c+1} : Finset ℕ).erase (b+1) = {5,c,c+1} := by ext t; simp; omega
      rw [hf,show (b+1)-((b)-7)=8 by omega]
      exact five_pair_eight_nonwin c (by omega) hce
  · constructor
    · intro h
      omega
    · intro h
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {5,b,c,c+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b) (by simp) (by omega)
      have hf : ({5,b,c,c+1} : Finset ℕ).erase (b) = {5,c,c+1} := by ext t; simp; omega
      rw [hf,show (b)-((b+1)-7)=6 by omega]
      exact five_pair_six_nonwin c (by omega) hce
  · constructor
    · intro h
      omega
    · intro h
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase (c) = {5,c+1,b,b+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
      have hf : ({5,c+1,b,b+1} : Finset ℕ).erase (c+1) = {5,b,b+1} := by ext t; simp; omega
      rw [hf,show (c+1)-((c)-7)=8 by omega]
      exact five_pair_eight_nonwin b (by omega) hbe
  · constructor
    · intro h
      omega
    · intro h
      have he : ({5,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {5,c,b,b+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (c) (by simp) (by omega)
      have hf : ({5,c,b,b+1} : Finset ℕ).erase (c) = {5,b,b+1} := by ext t; simp; omega
      rw [hf,show (c)-((c+1)-7)=6 by omega]
      exact five_pair_six_nonwin b (by omega) hbe

/-- The seven-counter residual from replying four then the missing mate.
All counter magnitudes are unbounded; eight is explicitly excluded. -/
theorem five_three_pairs_eight (b c e : ℕ) (hb : 6 ≤ b)
    (hbc : b+2 ≤ c) (hce : c+2 ≤ e)
    (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0)
    (hbn : b≠8) (hcn : c≠8) (hen : e≠8) :
    Position.value ⟨{5,b,b+1,c,c+1,e,e+1},8⟩ ≠ .win := by
  have hc10 : 10 ≤ c := by omega
  have hs : 8 ≤ ({5,b,b+1,c,c+1,e,e+1} : Finset ℕ).sum id :=
    (show 8 ≤ e by omega).trans
      (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp))
  apply (nonwin_step _ _ (by simp) hs).mpr
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx <;> subst x
  · constructor
    · intro _
      have he : ({5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase 5 = {b,b+1,c,c+1,e,e+1} := by
        ext t; simp; omega
      rw [he]
      exact DeficitTwo.three_pairs_three_nonwin b c e (by omega) hbc hce (by omega)
    · omega
  · constructor
    · intro h
      have hb6 : b=6 := by omega
      subst b
      have he : ({5,6,6+1,c,c+1,e,e+1} : Finset ℕ).erase (6) = {5,7,c,c+1,e,e+1} := by
        ext t; simp; omega
      rw [he]
      exact five_seven_two_pairs_two c e hc10 hce
    · intro h
      have he : ({5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b) = {5,b+1,c,c+1,e,e+1} := by
        ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({5,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b+1) = {5,c,c+1,e,e+1} := by
        ext t; simp; omega
      rw [hf,show (b+1)-((b)-8)=9 by omega]
      exact five_two_pairs_nine c e (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
  · constructor
    · intro h
      have hb6 : b=6 := by omega
      subst b
      have he : ({5,6,6+1,c,c+1,e,e+1} : Finset ℕ).erase (6+1) = {5,6,c,c+1,e,e+1} := by
        ext t; simp; omega
      rw [he]
      rw [TiedFour.three_pairs_one_draw 5 c e (by omega) (by omega) hce]
      decide
    · intro h
      have he : ({5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b+1) = {5,b,c,c+1,e,e+1} := by
        ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b) (by simp) (by omega)
      have hf : ({5,b,c,c+1,e,e+1} : Finset ℕ).erase (b) = {5,c,c+1,e,e+1} := by ext t; simp; omega
      rw [hf,show (b)-((b+1)-8)=7 by omega]
      exact five_two_pairs_seven c e (by omega) (by omega) (by omega) (by omega)
  · constructor
    · intro h
      omega
    · intro h
      have he : ({5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (c) = {5,c+1,b,b+1,e,e+1} := by
        ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
      have hf : ({5,c+1,b,b+1,e,e+1} : Finset ℕ).erase (c+1) = {5,b,b+1,e,e+1} := by
        ext t; simp; omega
      rw [hf,show (c+1)-((c)-8)=9 by omega]
      exact five_two_pairs_nine b e (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
  · constructor
    · intro h
      omega
    · intro h
      have he : ({5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (c+1) = {5,c,b,b+1,e,e+1} := by
        ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (c) (by simp) (by omega)
      have hf : ({5,c,b,b+1,e,e+1} : Finset ℕ).erase (c) = {5,b,b+1,e,e+1} := by ext t; simp; omega
      rw [hf,show (c)-((c+1)-8)=7 by omega]
      exact five_two_pairs_seven b e (by omega) (by omega) (by omega) (by omega)
  · constructor
    · intro h
      omega
    · intro h
      have he : ({5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (e) = {5,e+1,b,b+1,c,c+1} := by
        ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (e+1) (by simp) (by omega)
      have hf : ({5,e+1,b,b+1,c,c+1} : Finset ℕ).erase (e+1) = {5,b,b+1,c,c+1} := by
        ext t; simp; omega
      rw [hf,show (e+1)-((e)-8)=9 by omega]
      exact five_two_pairs_nine b c (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
  · constructor
    · intro h
      omega
    · intro h
      have he : ({5,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (e+1) = {5,e,b,b+1,c,c+1} := by
        ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (e) (by simp) (by omega)
      have hf : ({5,e,b,b+1,c,c+1} : Finset ℕ).erase (e) = {5,b,b+1,c,c+1} := by ext t; simp; omega
      rw [hf,show (e)-((e+1)-8)=7 by omega]
      exact five_two_pairs_seven b c (by omega) (by omega) (by omega) (by omega)

end CatchUp.AnchorFour
