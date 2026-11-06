/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ReserveTriangle.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.WholeTurn

/-!
# ReserveTriangle

A multi-turn defense beginning with pick five, covering all nine replies at the diagnosed
obstruction and symbolic related families.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.ReserveTriangle

open CatchUp.AdjacentPairRepair
open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (nonloss_of_continue)
open CatchUp.DeficitTwo (all_catching)
open CatchUp.DeficitTwo (adjacent_pair_loss)
open CatchUp.TiedFour (nonwin_step)
open CatchUp.AdjacentPairRepair (singleton_ge_nonwin)
open CatchUp.AdjacentPairRepair (adjacent_pair_draw)

/-- The equal-deficit orphan reserve tolerates two canonical pairs.
The close lower pair 10 is handled by an adaptive two-pick response. -/
theorem orphan_two_equal (z b c : ℕ) (hz : z=6 ∨ z=7)
    (hb : 10≤b) (hbc : b+2≤c) (hbe : b%2=0) (hce : c%2=0)
    (hb12 : b≠12) (hc12 : c≠12) :
    Position.value ⟨{z,b,b+1,c,c+1},z⟩ ≠ .win := by
  have hzlo : 2≤z := by omega
  have hzhi : z≤7 := by omega
  apply all_catching _ _ ⟨z,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> subst x
  · have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase z={b,b+1,c,c+1} := by
      ext t; simp; omega
    rw [he,Nat.sub_self,position_value_zero_deficit_eq_value,
      two_pairs_tied_draw b c (by omega) hbc]
    decide
  · have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase b={z,b+1,c,c+1} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({z,b+1,c,c+1}:Finset ℕ).erase (b+1)={z,c,c+1} := by
      ext t; simp; omega
    rw [hf,show b+1-(b-z)=z+1 by omega,orphan_plus_draw z c hzlo (by omega)]
    decide
  · have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase (b+1)={z,b,c,c+1} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({z,b,c,c+1}:Finset ℕ).erase b={z,c,c+1} := by
      ext t; simp; omega
    rw [hf,show b-(b+1-z)=z-1 by omega,orphan_minus_draw z c hzlo (by omega) (by omega)]
    decide
  · have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase c={z,b,b+1,c+1} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    have hf : ({z,b,b+1,c+1}:Finset ℕ).erase (c+1)={z,b,b+1} := by
      ext t; simp; omega
    rw [hf,show c+1-(c-z)=z+1 by omega,orphan_plus_draw z b hzlo (by omega)]
    decide
  · have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase (c+1)={z,b,b+1,c} := by
      ext t; simp; omega
    rw [he]
    by_cases hsep : 2*z-1≤b
    · apply nonloss_of_catch _ _ c (by simp) (by omega)
      have hf : ({z,b,b+1,c}:Finset ℕ).erase c={z,b,b+1} := by
        ext t; simp; omega
      rw [hf,show c-(c+1-z)=z-1 by omega,orphan_minus_draw z b hzlo (by omega) hsep]
      decide
    · have hb10 : b=10 := by omega
      subst b
      by_cases hfar : 18≤c
      · have hs : c≤({z,10,10+1,c}:Finset ℕ).sum id :=
          Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
        apply nonloss_of_continue _ _ 11 (by simp) (by omega) (by omega)
        have hf : ({z,10,10+1,c}:Finset ℕ).erase 11={z,10,c} := by
          ext t; simp; omega
        rw [hf]
        apply nonloss_of_catch _ _ c (by simp) (by omega)
        have hg : ({z,10,c}:Finset ℕ).erase c={z,10} := by
          ext t; simp; omega
        rw [hg,show c-(c+1-z-11)=z+10 by omega]
        have hh := WholeTurn.sum_draw ({z,10}:Finset ℕ)
        simpa [show z≠10 by omega] using ((Outcome.eq_draw_iff _).mp hh).2
      · have hc : c=14 ∨ c=16 := by omega
        rcases hz with rfl | rfl <;> rcases hc with rfl | rfl <;>
          rw [← Position.eval_eq_value] <;> decide +kernel

/-- A positive reserve surplus of three is nonwinning, with one high pair. -/
theorem orphan_one_three (z b : ℕ) (hz : 2≤z) (hb : z+3≤b) :
    Position.value ⟨{z,b,b+1},z+3⟩ ≠ .win := by
  have hs : b≤({z,b,b+1}:Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
  apply (nonwin_step _ _ (by simp) (by omega)).mpr
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx <;> subst x
  · constructor
    · intro _
      have he : ({z,b,b+1}:Finset ℕ).erase z={b,b+1} := by ext t; simp; omega
      rw [he,show z+3-z=3 by omega,adjacent_pair_loss b 3 (by omega) (by omega)]
      decide
    · omega
  · constructor
    · omega
    · intro _
      have he : ({z,b,b+1}:Finset ℕ).erase b={z,b+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({z,b+1}:Finset ℕ).erase (b+1)={z} := by ext t; simp; omega
      rw [hf]
      exact singleton_ge_nonwin z _ (by omega)
  · constructor
    · omega
    · intro _
      have he : ({z,b,b+1}:Finset ℕ).erase (b+1)={z,b} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ b (by simp) (by omega)
      have hf : ({z,b}:Finset ℕ).erase b={z} := by ext t; simp; omega
      rw [hf]
      exact singleton_ge_nonwin z _ (by omega)

/-- Two intact pairs preserve a reserve offset of two. -/
theorem orphan_two_plus (z b c : ℕ) (hz : 2≤z)
    (hb : z+3≤b) (hbc : b+2≤c) :
    Position.value ⟨{z,b,b+1,c,c+1},z+2⟩ ≠ .win := by
  have hs : b≤({z,b,b+1,c,c+1}:Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
  apply (nonwin_step _ _ (by simp) (by omega)).mpr
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> subst x
  · constructor
    · intro _
      have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase z={b,b+1,c,c+1} := by ext t; simp; omega
      rw [he,show z+2-z=2 by omega]
      exact two_pairs_deficit_two_nonwin b c (by omega) hbc
    · omega
  · constructor
    · omega
    · intro _
      have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase (b)={z,b+1,c,c+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({z,b+1,c,c+1}:Finset ℕ).erase (b+1)={z,c,c+1} := by ext t; simp; omega
      rw [hf,show (b+1)-((b)-(z+2))=z+3 by omega]
      exact orphan_one_three z c hz (by omega)
  · constructor
    · omega
    · intro _
      have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase (b+1)={z,b,c,c+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (b) (by simp) (by omega)
      have hf : ({z,b,c,c+1}:Finset ℕ).erase (b)={z,c,c+1} := by ext t; simp; omega
      rw [hf,show (b)-((b+1)-(z+2))=z+1 by omega]
      rw [orphan_plus_draw z c hz (by omega)]
      decide
  · constructor
    · omega
    · intro _
      have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase (c)={z,b,b+1,c+1} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
      have hf : ({z,b,b+1,c+1}:Finset ℕ).erase (c+1)={z,b,b+1} := by ext t; simp; omega
      rw [hf,show (c+1)-((c)-(z+2))=z+3 by omega]
      exact orphan_one_three z b hz (by omega)
  · constructor
    · omega
    · intro _
      have he : ({z,b,b+1,c,c+1}:Finset ℕ).erase (c+1)={z,b,b+1,c} := by ext t; simp; omega
      rw [he]
      apply nonloss_of_catch _ _ (c) (by simp) (by omega)
      have hf : ({z,b,b+1,c}:Finset ℕ).erase (c)={z,b,b+1} := by ext t; simp; omega
      rw [hf,show (c)-((c+1)-(z+2))=z+1 by omega]
      rw [orphan_plus_draw z b hz (by omega)]
      decide

/-- A six-or-seven orphan with three canonical pairs draws one below catching.
All pair choices reduce to the two offset reserves above. -/
theorem orphan_three_draw (z b c e : ℕ) (hz : z=6 ∨ z=7)
    (hb : 10≤b) (hbc : b+2≤c) (hce : c+2≤e)
    (hbe : b%2=0) (hceven : c%2=0) (hee : e%2=0)
    (hb12 : b≠12) (hc12 : c≠12) (he12 : e≠12) :
    Position.value ⟨{z,b,b+1,c,c+1,e,e+1},z+1⟩ = .draw := by
  have hzlo : 2≤z := by omega
  have hzhi : z≤7 := by omega
  have hs : b≤({z,b,b+1,c,c+1,e,e+1}:Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
  apply (Outcome.eq_draw_iff _).mpr
  constructor
  · apply nonloss_of_continue _ _ z (by simp) (by omega) (by omega)
    have he : ({z,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase z=
        {b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he,show z+1-z=1 by omega,TiedFour.three_pairs_one_draw b c e (by omega) hbc hce]
    decide
  · apply (nonwin_step _ _ (by simp) (by omega)).mpr
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx | hx | hx | hx | hx <;> subst x
    · constructor
      · intro _
        have he : ({z,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase z=
            {b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
        rw [he,show z+1-z=1 by omega,TiedFour.three_pairs_one_draw b c e (by omega) hbc hce]
        decide
      · omega
    · constructor
      · omega
      · intro _
        have he : ({z,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (b)={z,b+1,c,c+1,e,e+1} := by ext t; simp; omega
        rw [he]
        apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
        have hf : ({z,b+1,c,c+1,e,e+1}:Finset ℕ).erase (b+1)={z,c,c+1,e,e+1} := by
          ext t; simp; omega
        rw [hf,show (b+1)-((b)-(z+1))=z+2 by omega]
        exact orphan_two_plus z c e hzlo (by omega) (by omega)
    · constructor
      · omega
      · intro _
        have he : ({z,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (b+1)={z,b,c,c+1,e,e+1} := by ext t; simp; omega
        rw [he]
        apply nonloss_of_catch _ _ (b) (by simp) (by omega)
        have hf : ({z,b,c,c+1,e,e+1}:Finset ℕ).erase (b)={z,c,c+1,e,e+1} := by
          ext t; simp; omega
        rw [hf,show (b)-((b+1)-(z+1))=z+0 by omega]
        exact orphan_two_equal z c e hz (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega)
    · constructor
      · omega
      · intro _
        have he : ({z,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (c)={z,b,b+1,c+1,e,e+1} := by ext t; simp; omega
        rw [he]
        apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
        have hf : ({z,b,b+1,c+1,e,e+1}:Finset ℕ).erase (c+1)={z,b,b+1,e,e+1} := by
          ext t; simp; omega
        rw [hf,show (c+1)-((c)-(z+1))=z+2 by omega]
        exact orphan_two_plus z b e hzlo (by omega) (by omega)
    · constructor
      · omega
      · intro _
        have he : ({z,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (c+1)={z,b,b+1,c,e,e+1} := by ext t; simp; omega
        rw [he]
        apply nonloss_of_catch _ _ (c) (by simp) (by omega)
        have hf : ({z,b,b+1,c,e,e+1}:Finset ℕ).erase (c)={z,b,b+1,e,e+1} := by
          ext t; simp; omega
        rw [hf,show (c)-((c+1)-(z+1))=z+0 by omega]
        exact orphan_two_equal z b e hz (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega)
    · constructor
      · omega
      · intro _
        have he : ({z,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (e)={z,b,b+1,c,c+1,e+1} := by ext t; simp; omega
        rw [he]
        apply nonloss_of_catch _ _ (e+1) (by simp) (by omega)
        have hf : ({z,b,b+1,c,c+1,e+1}:Finset ℕ).erase (e+1)={z,b,b+1,c,c+1} := by
          ext t; simp; omega
        rw [hf,show (e+1)-((e)-(z+1))=z+2 by omega]
        exact orphan_two_plus z b c hzlo (by omega) (by omega)
    · constructor
      · omega
      · intro _
        have he : ({z,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (e+1)={z,b,b+1,c,c+1,e} := by ext t; simp; omega
        rw [he]
        apply nonloss_of_catch _ _ (e) (by simp) (by omega)
        have hf : ({z,b,b+1,c,c+1,e}:Finset ℕ).erase (e)={z,b,b+1,c,c+1} := by
          ext t; simp; omega
        rw [hf,show (e)-((e+1)-(z+1))=z+0 by omega]
        exact orphan_two_equal z b c hz (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega)

/-- The small balanced triangle has no winning move at offsets zero, two, or four. -/
theorem triangle_nonwin (d : ℕ) (hd : d=0 ∨ d=2 ∨ d=4) :
    Position.value ⟨{6,7,13},d⟩ ≠ .win := by
  rcases hd with rfl | rfl | rfl <;> rw [←Position.eval_eq_value] <;> decide +kernel

private theorem orphan_one_odd (z b d : ℕ) (hz : 2≤z) (hb : z+3≤b)
    (hd : d=1 ∨ d=3) :
    Position.value ⟨{z,b,b+1},z+d⟩ ≠ .win := by
  rcases hd with rfl | rfl
  · rw [orphan_plus_draw z b hz (by omega)]
    decide
  · exact orphan_one_three z b hz hb

private theorem pair_odd_nonwin (b d : ℕ) (hb : 3≤b) (hd : d=1 ∨ d=3) :
    Position.value ⟨{b,b+1},d⟩ ≠ .win := by
  rcases hd with rfl | rfl
  · rw [adjacent_pair_draw b (by omega)]
    decide
  · rw [adjacent_pair_loss b 3 (by omega) hb]
    decide

/-- One arbitrary high canonical pair permits both odd triangle offsets. -/
theorem triangle_one_nonwin (b d : ℕ) (hb : 10≤b) (hbe : b%2=0)
    (hb12 : b≠12) (hd : d=1 ∨ d=3) :
    Position.value ⟨{6,7,13,b,b+1},d⟩ ≠ .win := by
  have hnot13 : b≠13 ∧ b+1≠13 := by omega
  apply all_catching _ _ ⟨6,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> subst x
  · have he : ({6,7,13,b,b+1}:Finset ℕ).erase 6={7,13,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 13 (by simp) (by omega)
    have hf : ({7,13,b,b+1}:Finset ℕ).erase 13={7,b,b+1} := by ext t; simp; omega
    rw [hf,show 13-(6-d)=7+d by omega]
    exact orphan_one_odd 7 b d (by omega) (by omega) hd
  · have he : ({6,7,13,b,b+1}:Finset ℕ).erase 7={6,13,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 13 (by simp) (by omega)
    have hf : ({6,13,b,b+1}:Finset ℕ).erase 13={6,b,b+1} := by ext t; simp; omega
    rw [hf,show 13-(7-d)=6+d by omega]
    exact orphan_one_odd 6 b d (by omega) (by omega) hd
  · have he : ({6,7,13,b,b+1}:Finset ℕ).erase 13={6,7,b,b+1} := by ext t; simp; omega
    rw [he]
    have hs : 13≤({6,7,b,b+1}:Finset ℕ).sum id := by
      have hh : ({6,7}:Finset ℕ).sum id≤({6,7,b,b+1}:Finset ℕ).sum id :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by intro x hx; simp at hx ⊢; tauto) (by intros; exact Nat.zero_le _)
      have he : ({6,7}:Finset ℕ).sum id=13 := by decide +kernel
      rw [he] at hh
      exact hh
    apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
    have hf : ({6,7,b,b+1}:Finset ℕ).erase 6={7,b,b+1} := by ext t; simp; omega
    rw [hf]
    apply nonloss_of_catch _ _ 7 (by simp) (by omega)
    have hg : ({7,b,b+1}:Finset ℕ).erase 7={b,b+1} := by ext t; simp; omega
    rw [hg,show 7-(13-d-6)=d by omega]
    exact pair_odd_nonwin b d (by omega) hd
  · have he : ({6,7,13,b,b+1}:Finset ℕ).erase b={6,7,13,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({6,7,13,b+1}:Finset ℕ).erase (b+1)={6,7,13} := by ext t; simp; omega
    rw [hf,show b+1-(b-d)=d+1 by omega]
    exact triangle_nonwin (d+1) (by omega)
  · have he : ({6,7,13,b,b+1}:Finset ℕ).erase (b+1)={6,7,13,b} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({6,7,13,b}:Finset ℕ).erase b={6,7,13} := by ext t; simp; omega
    rw [hf,show b-(b+1-d)=d-1 by omega]
    exact triangle_nonwin (d-1) (by omega)

private theorem separated_four_nonwin (b : ℕ) (hb : 20≤b) :
    Position.value ⟨{7,13,b,b+1},5⟩ ≠ .win := by
  apply all_catching _ _ ⟨7,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  · have he : ({7,13,b,b+1}:Finset ℕ).erase 7={13,b,b+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 13 (by simp) (by omega)
    have hf : ({13,b,b+1}:Finset ℕ).erase 13={b,b+1} := by ext t; simp; omega
    rw [hf,show 13-(7-5)=11 by omega,adjacent_pair_loss b 11 (by omega) (by omega)]
    decide
  · have he : ({7,13,b,b+1}:Finset ℕ).erase 13={7,b,b+1} := by ext t; simp; omega
    rw [he]
    have hs : b≤({7,b,b+1}:Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 7 (by simp) (by omega) (by omega)
    have hf : ({7,b,b+1}:Finset ℕ).erase 7={b,b+1} := by ext t; simp; omega
    rw [hf,show 13-5-7=1 by omega,adjacent_pair_draw b (by omega)]
    decide
  · have he : ({7,13,b,b+1}:Finset ℕ).erase b={7,13,b+1} := by ext t; simp; omega
    rw [he]
    have hs : b+1≤({7,13,b+1}:Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 13 (by simp) (by omega) (by omega)
    have hf : ({7,13,b+1}:Finset ℕ).erase 13={7,b+1} := by ext t; simp; omega
    rw [hf]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hg : ({7,b+1}:Finset ℕ).erase (b+1)={7} := by ext t; simp; omega
    rw [hg]
    exact singleton_ge_nonwin 7 _ (by omega)
  · have he : ({7,13,b,b+1}:Finset ℕ).erase (b+1)={7,13,b} := by ext t; simp; omega
    rw [he]
    have hs : b≤({7,13,b}:Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 13 (by simp) (by omega) (by omega)
    have hf : ({7,13,b}:Finset ℕ).erase 13={7,b} := by ext t; simp; omega
    rw [hf]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hg : ({7,b}:Finset ℕ).erase b={7} := by ext t; simp; omega
    rw [hg]
    exact singleton_ge_nonwin 7 _ (by omega)

/-- The one-pair reserve is drawn uniformly in its high counter labels. -/
theorem triangle_one_draw (b : ℕ) (hb : 10≤b) (hbe : b%2=0) (hb12 : b≠12) :
    Position.value ⟨{6,7,13,b,b+1},1⟩ = .draw := by
  apply (Outcome.eq_draw_iff _).mpr
  refine ⟨?_,triangle_one_nonwin b 1 hb hbe hb12 (by omega)⟩
  by_cases hfar : 20≤b
  · apply nonloss_of_catch _ _ 6 (by simp) (by omega)
    have he : ({6,7,13,b,b+1}:Finset ℕ).erase 6={7,13,b,b+1} := by ext t; simp; omega
    rw [he]
    exact separated_four_nonwin b hfar
  · have hcases : b=10 ∨ b=14 ∨ b=16 ∨ b=18 := by omega
    rcases hcases with rfl | rfl | rfl | rfl <;>
      rw [←Position.eval_eq_value] <;> decide +kernel

/-- The triangle plus two canonical pairs is nonwinning at tied or deficit-two positions. -/
theorem triangle_two_nonwin (b c d : ℕ) (hb : 10≤b) (hbc : b+2≤c)
    (hbe : b%2=0) (hce : c%2=0) (hb12 : b≠12) (hc12 : c≠12)
    (hd : d=0 ∨ d=2) :
    Position.value ⟨{6,7,13,b,b+1,c,c+1},d⟩ ≠ .win := by
  apply all_catching _ _ ⟨6,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({6,7,13,b,b+1,c,c+1}:Finset ℕ).erase 6={7,13,b,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 13 (by simp) (by omega)
    have hf : ({7,13,b,b+1,c,c+1}:Finset ℕ).erase 13={7,b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show 13-(6-d)=7+d by omega]
    rcases hd with rfl | rfl
    · exact orphan_two_equal 7 b c (by omega) hb hbc hbe hce hb12 hc12
    · exact orphan_two_plus 7 b c (by omega) (by omega) hbc
  · have he : ({6,7,13,b,b+1,c,c+1}:Finset ℕ).erase 7={6,13,b,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 13 (by simp) (by omega)
    have hf : ({6,13,b,b+1,c,c+1}:Finset ℕ).erase 13={6,b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show 13-(7-d)=6+d by omega]
    rcases hd with rfl | rfl
    · exact orphan_two_equal 6 b c (by omega) hb hbc hbe hce hb12 hc12
    · exact orphan_two_plus 6 b c (by omega) (by omega) hbc
  · have he : ({6,7,13,b,b+1,c,c+1}:Finset ℕ).erase 13={6,7,b,b+1,c,c+1} := by
      ext t; simp; omega
    rw [he]
    have hs : 13≤({6,7,b,b+1,c,c+1}:Finset ℕ).sum id := by
      have hh : ({6,7}:Finset ℕ).sum id≤({6,7,b,b+1,c,c+1}:Finset ℕ).sum id :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by intro x hx; simp at hx ⊢; tauto) (by intros; exact Nat.zero_le _)
      have hv : ({6,7}:Finset ℕ).sum id=13 := by decide +kernel
      omega
    apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
    have hf : ({6,7,b,b+1,c,c+1}:Finset ℕ).erase 6={7,b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf]
    apply nonloss_of_catch _ _ 7 (by simp) (by omega)
    have hg : ({7,b,b+1,c,c+1}:Finset ℕ).erase 7={b,b+1,c,c+1} := by ext t; simp; omega
    rw [hg,show 7-(13-d-6)=d by omega]
    rcases hd with rfl | rfl
    · rw [position_value_zero_deficit_eq_value,two_pairs_tied_draw b c (by omega) hbc]
      decide
    · exact two_pairs_deficit_two_nonwin b c (by omega) hbc
  · have he : ({6,7,13,b,b+1,c,c+1}:Finset ℕ).erase (b)={6,7,13,b+1,c,c+1} := by ext t; simp; omega
    rw [he]
    have hf : ({6,7,13,b+1,c,c+1}:Finset ℕ).erase (b+1)={6,7,13,c,c+1} := by ext t; simp; omega
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    rw [hf,show (b+1)-((b)-d)=d+1 by omega]
    exact triangle_one_nonwin c (d+1) (by omega) (by omega) (by omega) (by omega)
  · have he : ({6,7,13,b,b+1,c,c+1}:Finset ℕ).erase (b+1)={6,7,13,b,c,c+1} := by ext t; simp; omega
    rw [he]
    have hf : ({6,7,13,b,c,c+1}:Finset ℕ).erase (b)={6,7,13,c,c+1} := by ext t; simp; omega
    rcases hd with rfl | rfl
    · have hs : 13≤({6,7,13,c,c+1}:Finset ℕ).sum id :=
        Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
      have ht : (({6,7,13,b,c,c+1}:Finset ℕ).erase (b)).sum id+(b)=
          ({6,7,13,b,c,c+1}:Finset ℕ).sum id := by
        simpa using Finset.sum_erase_add ({6,7,13,b,c,c+1}:Finset ℕ) id
          (show (b)∈({6,7,13,b,c,c+1}:Finset ℕ) by simp)
      rw [hf] at ht
      apply nonloss_of_continue _ _ (b) (by simp) (by omega) (by omega)
      rw [hf,show (b+1)-0-(b)=1 by omega,triangle_one_draw c (by omega) (by omega) (by omega)]
      decide
    · apply nonloss_of_catch _ _ (b) (by simp) (by omega)
      rw [hf,show (b)-((b+1)-2)=1 by omega,
        triangle_one_draw c (by omega) (by omega) (by omega)]
      decide
  · have he : ({6,7,13,b,b+1,c,c+1}:Finset ℕ).erase (c)={6,7,13,b,b+1,c+1} := by ext t; simp; omega
    rw [he]
    have hf : ({6,7,13,b,b+1,c+1}:Finset ℕ).erase (c+1)={6,7,13,b,b+1} := by ext t; simp; omega
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    rw [hf,show (c+1)-((c)-d)=d+1 by omega]
    exact triangle_one_nonwin b (d+1) (by omega) (by omega) (by omega) (by omega)
  · have he : ({6,7,13,b,b+1,c,c+1}:Finset ℕ).erase (c+1)={6,7,13,b,b+1,c} := by ext t; simp; omega
    rw [he]
    have hf : ({6,7,13,b,b+1,c}:Finset ℕ).erase (c)={6,7,13,b,b+1} := by ext t; simp; omega
    rcases hd with rfl | rfl
    · have hs : 13≤({6,7,13,b,b+1}:Finset ℕ).sum id :=
        Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
      have ht : (({6,7,13,b,b+1,c}:Finset ℕ).erase (c)).sum id+(c)=
          ({6,7,13,b,b+1,c}:Finset ℕ).sum id := by
        simpa using Finset.sum_erase_add ({6,7,13,b,b+1,c}:Finset ℕ) id
          (show (c)∈({6,7,13,b,b+1,c}:Finset ℕ) by simp)
      rw [hf] at ht
      apply nonloss_of_continue _ _ (c) (by simp) (by omega) (by omega)
      rw [hf,show (c+1)-0-(c)=1 by omega,triangle_one_draw b (by omega) (by omega) (by omega)]
      decide
    · apply nonloss_of_catch _ _ (c) (by simp) (by omega)
      rw [hf,show (c)-((c+1)-2)=1 by omega,
        triangle_one_draw b (by omega) (by omega) (by omega)]
      decide

/-- A balanced {6,7,13} reserve protects against every pick among three arbitrary
canonical pairs above 10, excluding the overlapping start 12. -/
theorem triangle_three_nonwin (b c e : ℕ)
    (hb : 10≤b) (hbc : b+2≤c) (hce : c+2≤e)
    (hbe : b%2=0) (hceven : c%2=0) (hee : e%2=0)
    (hb12 : b≠12) (hc12 : c≠12) (he12 : e≠12) :
    Position.value ⟨{6,7,13,b,b+1,c,c+1,e,e+1},1⟩ ≠ .win := by
  apply all_catching _ _ ⟨6,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase 6={7,13,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 13 (by simp) (by omega)
    have hf : ({7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase 13={7,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show 13-(6-1)=7+1 by omega,
      orphan_three_draw 7 b c e (by omega) hb hbc hce hbe hceven hee hb12 hc12 he12]
    decide
  · have he : ({6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase 7={6,13,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ 13 (by simp) (by omega)
    have hf : ({6,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase 13={6,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show 13-(7-1)=6+1 by omega,
      orphan_three_draw 6 b c e (by omega) hb hbc hce hbe hceven hee hb12 hc12 he12]
    decide
  · have he : ({6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase 13={6,7,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    have hs : e≤({6,7,b,b+1,c,c+1,e,e+1}:Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ => Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
    have hf : ({6,7,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase 6={7,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf]
    apply nonloss_of_catch _ _ 7 (by simp) (by omega)
    have hg : ({7,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase 7={b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hg,show 7-(13-1-6)=1 by omega,TiedFour.three_pairs_one_draw b c e (by omega) hbc hce]
    decide
  · have he : ({6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (b)={6,7,13,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({6,7,13,b+1,c,c+1,e,e+1}:Finset ℕ).erase (b+1)={6,7,13,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show (b+1)-((b)-1)=2 by omega]
    exact triangle_two_nonwin c e 2 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (b+1)={6,7,13,b,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b) (by simp) (by omega)
    have hf : ({6,7,13,b,c,c+1,e,e+1}:Finset ℕ).erase (b)={6,7,13,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show (b)-((b+1)-1)=0 by omega]
    exact triangle_two_nonwin c e 0 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (c)={6,7,13,b,b+1,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    have hf : ({6,7,13,b,b+1,c+1,e,e+1}:Finset ℕ).erase (c+1)={6,7,13,b,b+1,e,e+1} := by ext t; simp; omega
    rw [hf,show (c+1)-((c)-1)=2 by omega]
    exact triangle_two_nonwin b e 2 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (c+1)={6,7,13,b,b+1,c,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (c) (by simp) (by omega)
    have hf : ({6,7,13,b,b+1,c,e,e+1}:Finset ℕ).erase (c)={6,7,13,b,b+1,e,e+1} := by ext t; simp; omega
    rw [hf,show (c)-((c+1)-1)=0 by omega]
    exact triangle_two_nonwin b e 0 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (e)={6,7,13,b,b+1,c,c+1,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (e+1) (by simp) (by omega)
    have hf : ({6,7,13,b,b+1,c,c+1,e+1}:Finset ℕ).erase (e+1)={6,7,13,b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show (e+1)-((e)-1)=2 by omega]
    exact triangle_two_nonwin b c 2 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · have he : ({6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase (e+1)={6,7,13,b,b+1,c,c+1,e} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (e) (by simp) (by omega)
    have hf : ({6,7,13,b,b+1,c,c+1,e}:Finset ℕ).erase (e)={6,7,13,b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf,show (e)-((e+1)-1)=0 by omega]
    exact triangle_two_nonwin b c 0 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)


/-- Pick five safely converts an entire family of deficit-four positions into
the triangle defense, rather than only handling the concrete diagnostic. -/
theorem uniform_pick_five (b c e : ℕ)
    (hb : 10≤b) (hbc : b+2≤c) (hce : c+2≤e)
    (hbe : b%2=0) (hceven : c%2=0) (hee : e%2=0)
    (hb12 : b≠12) (hc12 : c≠12) (he12 : e≠12) :
    (⟨{5,6,7,13,b,b+1,c,c+1,e,e+1},4⟩:Position).moveOutcome 5 ≠ .loss := by
  have he : ({5,6,7,13,b,b+1,c,c+1,e,e+1}:Finset ℕ).erase 5=
      {6,7,13,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
  simpa only [Position.moveOutcome,Position.afterPick,show ¬5<4 by omega,
    ite_false,he,show 5-4=1 by omega,Outcome.neg_ne_loss_iff] using
    triangle_three_nonwin b c e hb hbc hce hbe hceven hee hb12 hc12 he12

/-- The actual child after the proposed pick five. -/
def afterFive : GamePosition := ⟨⟨{6,7,10,11,13,20,21,40,41},1⟩,.p1⟩

theorem after_five_nonwin : afterFive.toPosition.value ≠ .win := by
  have h := triangle_three_nonwin 10 20 40 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have he : ({6,7,13,10,10+1,20,20+1,40,40+1}:Finset ℕ)=afterFive.remaining := by
    decide +kernel
  rw [he] at h
  exact h

/-- The uniform triangle theorem protects the waiting defender at the known child. -/
theorem after_five_safe : CanAvoidLoss .p2 afterFive := by
  rw [can_avoid_loss_iff_value]
  change afterFive.toPosition.value ≠ .win
  exact after_five_nonwin

/-- No opening among the nine remaining counters is omitted from the guarantee. -/
theorem all_nine_replies_safe :
    ∀ x ∈ afterFive.remaining, CanAvoidLoss .p2 (afterFive.afterPick x) := by
  have ht : ¬afterFive.IsTerminal := by
    rw [GamePosition.not_is_terminal_iff]
    decide +kernel
  intro x hx
  exact (can_avoid_loss_iff_forall_safe_moves .p2 afterFive ht (by decide +kernel)).mp
    after_five_safe x hx

/-- Pick five is a legal safe choice at the earlier mate obstruction. -/
theorem pick_five_safe : CanAvoidLoss .p2 SevenPairTest.beforeBadMate := by
  have ht : ¬SevenPairTest.beforeBadMate.IsTerminal := by
    rw [GamePosition.not_is_terminal_iff]
    decide +kernel
  rw [can_avoid_loss_iff_exists_safe_move .p2 SevenPairTest.beforeBadMate ht (by rfl)]
  refine ⟨5,?_,?_⟩
  · unfold GamePosition.LegalMove
    decide +kernel
  · have he : SevenPairTest.beforeBadMate.afterPick 5=afterFive := by decide +kernel
    rw [he]
    exact after_five_safe

/-- The selected move itself avoids loss, not just some alternative at that position. -/
theorem pick_five_move_nonloss :
    SevenPairTest.beforeBadMate.toPosition.moveOutcome 5 ≠ .loss := by
  have he : SevenPairTest.beforeBadMate.toPosition.afterPick 5=afterFive.toPosition := by
    decide +kernel
  simp only [Position.moveOutcome,
    show ¬5<SevenPairTest.beforeBadMate.deficit by decide +kernel,
    ite_false,he,Outcome.neg_ne_loss_iff]
  exact after_five_nonwin

/-- The same nonwinning guarantee under the frozen literal score evaluator. -/
theorem after_five_reference_nonwin :
    valueAux {6,7,10,11,13,20,21,40,41} 0 1 false ≠ .win := by
  rw [←Position.value_eq_value_aux _ 0 1 (by omega)]
  exact after_five_nonwin
open CatchUp.SevenPairTest (first_transition)
open CatchUp.SevenPairTest (four_transition)
open CatchUp.SevenPairTest (return_transition)
/-- The repaired decision is safe at every member of the old unbounded counterplay.
This asserts safety at the reached node, not at every choice from the initial support. -/
theorem uniform_repaired_branch (q : ℕ) (hq : 42≤q) :
    let p := (SevenPairTest.start q).afterPicks [q,4,q+1,12]
    p.toMove=.p2 ∧ p.toPosition.moveOutcome 5≠.loss ∧ CanAvoidLoss .p2 (p.afterPick 5) := by
  have he : SevenPairTest.afterReturn.afterPick 12=SevenPairTest.beforeBadMate := by
    decide +kernel
  have hf : SevenPairTest.beforeBadMate.afterPick 5=afterFive := by decide +kernel
  simp only [GamePosition.after_picks_cons,GamePosition.after_picks_nil,
    first_transition q hq,four_transition q hq,return_transition q hq,he,hf]
  exact ⟨rfl,pick_five_move_nonloss,after_five_safe⟩
end CatchUp.ReserveTriangle
