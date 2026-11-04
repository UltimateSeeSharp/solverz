/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/FivePair.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.FivePairLeaves

/-!
# FivePair

All one-pair reserves from [4,15] are defended at deficits one and three, yielding [4,15] nonwinning
at deficit two and [3,15] nonloss at deficit one.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.FivePair

open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (all_catching)
open CatchUp.DeficitTwo (nonloss_of_continue)
open CatchUp.FivePair (four_zero_of_lt)
open CatchUp.FivePair (four_two_of_lt)
open CatchUp.FivePair (four_four_of_lt)

theorem four_zero_draw (i j : Fin 6) (hne : i ≠ j) :
    Position.value ⟨fourReserve i j,0⟩ = .draw := by
  by_cases hij : i < j
  · exact four_zero_of_lt i j hij
  · rw [four_reserve_comm]
    exact four_zero_of_lt j i (by omega)

theorem four_two_nonwin (i j : Fin 6) (hne : i ≠ j) :
    Position.value ⟨fourReserve i j,2⟩ ≠ .win := by
  by_cases hij : i < j
  · exact four_two_of_lt i j hij
  · rw [four_reserve_comm]
    exact four_two_of_lt j i (by omega)

theorem four_four_nonwin (i j : Fin 6) (hne : i ≠ j)
    (hex : ¬ (i.val = 1 ∧ j.val = 4 ∨ i.val = 4 ∧ j.val = 1)) :
    Position.value ⟨fourReserve i j,4⟩ ≠ .win := by
  by_cases hij : i < j
  · exact four_four_of_lt i j hij (by omega)
  · rw [four_reserve_comm]
    exact four_four_of_lt j i (by omega) (by omega)

/-- A mate reply is legal, ends the defender's turn, and leaves deficit `d±1`.
The following nonwinning claim is used only for a strictly smaller position. -/
theorem mate_safety (i j : Fin 6) (x d : ℕ) (hx : x ∈ reserve i)
    (hd : d = 1 ∨ d = 3) (hj : j.val = (x-4)/2)
    (hr : Position.value ⟨fourReserve i j,if x%2=0 then d+1 else d-1⟩ ≠ .win) :
    Position.value ⟨(reserve i).erase x,x-d⟩ ≠ .loss := by
  have hm := mate_deficit x d (mem_range i x hx).1 (by omega)
  apply nonloss_of_catch _ _ (mate x) (mate_legal i x hx) hm.1
  have hs : ((reserve i).erase x).erase (mate x) = fourReserve i j := by
    simpa only [fourReserve,pairStart,hj] using erase_mates_eq i x hx
  rw [hs,hm.2]
  exact hr

/-- After the opponent's `12` with pair `{6,7}` absent, take `4` and then `8`.
The first pick continues the same turn. -/
theorem repair_twelve : Position.value ⟨(reserve 1).erase 12,9⟩ ≠ .loss := by
  have he : ((reserve 1).erase 12).erase 4 = {5,8,9,10,11,13,14,15} := by decide +kernel
  have hf : ({5,8,9,10,11,13,14,15} : Finset ℕ).erase 8 = {5,9,10,11,13,14,15} := by
    decide +kernel
  have hl : Position.value ⟨{5,9,10,11,13,14,15},3⟩ ≠ .win := by
    rw [nonwin_iff_check]
    decide +kernel
  apply nonloss_of_continue _ _ 4 (by decide +kernel) (by omega) (by decide +kernel)
  rw [he]
  apply nonloss_of_catch _ _ 8 (by decide +kernel) (by omega)
  simpa only [hf] using hl

/-- After the opponent's `6` with pair `{12,13}` absent, take `4`. -/
theorem repair_six : Position.value ⟨(reserve 4).erase 6,3⟩ ≠ .loss := by
  apply nonloss_of_catch _ _ 4 (by decide +kernel) (by omega)
  have he : ((reserve 4).erase 6).erase 4 = {5,7,8,9,10,11,14,15} := by decide +kernel
  rw [he,nonwin_iff_check]
  decide +kernel

/-- Every one-pair deletion from `[4,15]` is nonwinning at deficit one or three.
All ten legal first picks are covered. Only the two diagnosed nodes depart
from the mate response. -/
theorem reserve_nonwin (i : Fin 6) (d : ℕ) (hd : d = 1 ∨ d = 3) :
    Position.value ⟨reserve i,d⟩ ≠ .win := by
  apply all_catching _ _ (reserve_nonempty i)
  · intro x hx
    have := mem_range i x hx
    omega
  intro x hx
  by_cases hbad : d = 3 ∧ (i.val = 1 ∧ x = 12 ∨ i.val = 4 ∧ x = 6)
  · rcases hbad with ⟨rfl,hbad | hbad⟩
    · obtain ⟨hi,rfl⟩ := hbad
      have hi' : i = 1 := Fin.ext hi
      subst i
      exact repair_twelve
    · obtain ⟨hi,rfl⟩ := hbad
      have hi' : i = 4 := Fin.ext hi
      subst i
      exact repair_six
  · have hidx := picked_pair_index i x hx
    let j : Fin 6 := ⟨(x-4)/2,hidx.1⟩
    have hne : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [j] at hv
      omega
    apply mate_safety i j x d hx hd rfl
    by_cases heven : x%2 = 0
    · rw [ite_eq_left heven]
      rcases hd with rfl | rfl
      · exact four_two_nonwin i j hne
      · apply four_four_nonwin i j hne
        intro hex
        apply hbad
        refine ⟨rfl,?_⟩
        have hj : j.val = (x-4)/2 := rfl
        rcases hex with hex | hex
        · left; constructor
          · exact hex.1
          · omega
        · right; constructor
          · exact hex.1
          · omega
    · rw [ite_eq_right heven]
      rcases hd with rfl | rfl
      · rw [show 1-1=0 by omega,four_zero_draw i j hne]
        decide
      · exact four_two_nonwin i j hne

/-- The first pair-response round leaves exactly one of the five-pair reserves. -/
theorem pool_erase_mates (x : ℕ) (hx : 4 ≤ x ∧ x ≤ 15) :
    ((Finset.Icc 4 15).erase x).erase (mate x) =
      removePair (Finset.Icc 4 15) (4+2*((x-4)/2)) := by
  ext t
  simp only [removePair,Finset.mem_erase,Finset.mem_Icc]
  unfold mate
  split_ifs <;> omega

/-- Nonwinning at size fifteen, proved by two pair-response rounds and the
shared smaller leaves. This does not assume any universal interval claim. -/
theorem interval_fifteen_nonwin : Position.value ⟨Finset.Icc 4 15,2⟩ ≠ .win := by
  apply all_catching _ _ ⟨4,by decide +kernel⟩
  · intro x hx
    have := Finset.mem_Icc.mp hx
    omega
  intro x hx
  have hxr := Finset.mem_Icc.mp hx
  let j : Fin 6 := ⟨(x-4)/2,by omega⟩
  have hmate : mate x ∈ (Finset.Icc 4 15).erase x := by
    simp only [Finset.mem_erase,Finset.mem_Icc]
    unfold mate
    split_ifs <;> omega
  have hm := mate_deficit x 2 hxr.1 (by omega)
  apply nonloss_of_catch _ _ (mate x) hmate hm.1
  have hs : ((Finset.Icc 4 15).erase x).erase (mate x) = reserve j := by
    simpa only [reserve,pairStart,j] using pool_erase_mates x hxr
  rw [hs,hm.2]
  apply reserve_nonwin j
  by_cases heven : x%2=0 <;> simp [heven]

/-- Consequence for the original first-pair subproblem: choosing `3` avoids
loss. Its opposite nonloss direction is not supplied by this theorem. -/
theorem first_pair_fifteen_nonloss : Position.value ⟨Finset.Icc 3 15,1⟩ ≠ .loss :=
  DeficitTwo.first_pair_nonloss_of_interval_nonwin 15 (by omega) interval_fifteen_nonwin

end CatchUp.FivePair
