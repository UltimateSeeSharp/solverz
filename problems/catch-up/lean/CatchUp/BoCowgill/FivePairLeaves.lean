/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/FivePairLeaves.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DeficitTwo

/-!
# Five-pair reserves for the size-fifteen interval

The reserve deletes any one of the six actual adjacent pairs in `[4,15]`.
The opponent is unrestricted. Whole-pair replies reduce the ten-counter
positions to shared eight-counter leaves, with two explicit adaptive repairs.
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

def removePair (S : Finset ℕ) (a : ℕ) : Finset ℕ := (S.erase a).erase (a+1)

def pairStart (i : Fin 6) : ℕ := 4+2*i.val

def reserve (i : Fin 6) : Finset ℕ := removePair (Finset.Icc 4 15) (pairStart i)

def fourReserve (i j : Fin 6) : Finset ℕ := removePair (reserve i) (pairStart j)

def mate (x : ℕ) : ℕ := if x%2=0 then x+1 else x-1

theorem mate_legal (i : Fin 6) (x : ℕ) (hx : x ∈ reserve i) :
    mate x ∈ (reserve i).erase x := by
  simp only [reserve, removePair, pairStart, Finset.mem_erase, Finset.mem_Icc] at hx ⊢
  unfold mate
  split_ifs <;> omega

theorem mem_range (i : Fin 6) (x : ℕ) (hx : x ∈ reserve i) : 4 ≤ x ∧ x ≤ 15 := by
  simp only [reserve, removePair, Finset.mem_erase, Finset.mem_Icc] at hx
  exact hx.2.2

theorem picked_pair_index (i : Fin 6) (x : ℕ) (hx : x ∈ reserve i) :
    (x-4)/2 < 6 ∧ (x-4)/2 ≠ i.val := by
  simp only [reserve, removePair, pairStart, Finset.mem_erase, Finset.mem_Icc] at hx
  omega

theorem erase_mates_eq (i : Fin 6) (x : ℕ) (hx : x ∈ reserve i) :
    ((reserve i).erase x).erase (mate x) = removePair (reserve i) (4+2*((x-4)/2)) := by
  ext t
  simp only [reserve, removePair, pairStart, Finset.mem_erase, Finset.mem_Icc] at hx ⊢
  unfold mate
  split_ifs <;> omega

theorem mate_deficit (x d : ℕ) (hx : 4 ≤ x) (hd : 1 ≤ d ∧ d ≤ 3) :
    x-d ≤ mate x ∧ mate x-(x-d) = if x%2=0 then d+1 else d-1 := by
  unfold mate
  split_ifs <;> omega

theorem four_reserve_comm (i j : Fin 6) : fourReserve i j = fourReserve j i := by
  ext t
  simp only [fourReserve, reserve, removePair, Finset.mem_erase]
  tauto

theorem reserve_nonempty (i : Fin 6) : (reserve i).Nonempty := by
  fin_cases i <;> decide +kernel

/-- Shared finite leaves: exactly two pairs deleted from the six-pair pool.
These are bounded exact results, not an arbitrary-support tied-game theorem. -/
private def drawOpening (i j : Fin 6) : ℕ :=
  if i.val = 0 then if j.val = 1 then 11 else 7 else 5

set_option maxHeartbeats 4000000 in
theorem four_zero_of_lt (i j : Fin 6) (hij : i < j) :
    Position.value ⟨fourReserve i j,0⟩ = .draw := by
  have hm : drawOpening i j ∈ fourReserve i j := by
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals decide +kernel
  rw [position_value_zero_deficit_eq_value]
  apply (value_eq_draw_iff_exists_draw_after_opening _ ⟨drawOpening i j,hm⟩).mpr
  refine ⟨drawOpening i j,hm,?_⟩
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals rw [← Position.eval_eq_value]; decide +kernel

theorem nonwin_iff_check (p : Position) : p.value ≠ .win ↔
    CatchUpSearch.CanAvoidLossClassifier.check .p2 ⟨p,.p1⟩ = true := by
  rw [CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff,can_avoid_loss_iff_value]
  simp

set_option maxHeartbeats 4000000 in
theorem four_four_of_lt (i j : Fin 6) (hij : i < j)
    (hex : ¬ (i.val = 1 ∧ j.val = 4)) :
    Position.value ⟨fourReserve i j,4⟩ ≠ .win := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals norm_num at hex
  all_goals rw [nonwin_iff_check]; decide +kernel

/-- This part reuses the symbolic four-pair theorem rather than recomputing its outcomes. -/
theorem four_two_of_lt (i j : Fin 6) (hij : i < j) :
    Position.value ⟨fourReserve i j,2⟩ ≠ .win := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · change Position.value ⟨fourReserve 0 1,2⟩ ≠ .win
    have hs : fourReserve 0 1 = {8,9,10,11,12,13,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 8 10 12 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 0 2,2⟩ ≠ .win
    have hs : fourReserve 0 2 = {6,7,10,11,12,13,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 6 10 12 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 0 3,2⟩ ≠ .win
    have hs : fourReserve 0 3 = {6,7,8,9,12,13,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 6 8 12 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 0 4,2⟩ ≠ .win
    have hs : fourReserve 0 4 = {6,7,8,9,10,11,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 6 8 10 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 0 5,2⟩ ≠ .win
    have hs : fourReserve 0 5 = {6,7,8,9,10,11,12,13} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 6 8 10 12 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 1 2,2⟩ ≠ .win
    have hs : fourReserve 1 2 = {4,5,10,11,12,13,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 10 12 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 1 3,2⟩ ≠ .win
    have hs : fourReserve 1 3 = {4,5,8,9,12,13,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 8 12 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 1 4,2⟩ ≠ .win
    have hs : fourReserve 1 4 = {4,5,8,9,10,11,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 8 10 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 1 5,2⟩ ≠ .win
    have hs : fourReserve 1 5 = {4,5,8,9,10,11,12,13} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 8 10 12 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 2 3,2⟩ ≠ .win
    have hs : fourReserve 2 3 = {4,5,6,7,12,13,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 6 12 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 2 4,2⟩ ≠ .win
    have hs : fourReserve 2 4 = {4,5,6,7,10,11,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 6 10 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 2 5,2⟩ ≠ .win
    have hs : fourReserve 2 5 = {4,5,6,7,10,11,12,13} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 6 10 12 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 3 4,2⟩ ≠ .win
    have hs : fourReserve 3 4 = {4,5,6,7,8,9,14,15} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 6 8 14 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 3 5,2⟩ ≠ .win
    have hs : fourReserve 3 5 = {4,5,6,7,8,9,12,13} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 6 8 12 (by omega) (by omega) (by omega) (by omega)
  · change Position.value ⟨fourReserve 4 5,2⟩ ≠ .win
    have hs : fourReserve 4 5 = {4,5,6,7,8,9,10,11} := by decide +kernel
    rw [hs]
    exact DeficitTwo.four_pairs_two_nonwin 4 6 8 10 (by omega) (by omega) (by omega) (by omega)

end CatchUp.FivePair
