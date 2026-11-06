/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseBlockMass.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DenseTerminalReduction

/-!
# Exact-block mass and small residuals

These cardinality bounds use no outcome, parity, or maximal-block assumption.
They bound the ambient interval once a large member of an exact block and a
small residual have been supplied. They do not prove strategic preservation.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseBlockMass

/-- The other distinct positive block members have triangular mass at most the hole budget. -/
theorem exact_block_card_bound
    (N h d b : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hB : B ⊆ S) (hsum : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hnear : d - h ≤ b) : B.card * (B.card - 1) ≤ 2 * h := by
  have hsmall : B.erase b ⊆ Icc 1 N := by
    intro x hx
    exact hS (hB (mem_of_mem_erase hx))
  have htri := DenseTerminalReduction.interval_subset_sum_lower N (B.erase b) hsmall
  have hsumErase := Finset.sum_erase_add B (fun x : ℕ ↦ x) hb
  try simp only at hsumErase
  rw [hsum] at hsumErase
  have hmass : (B.erase b).sum (fun x ↦ x) ≤ h := by omega
  have hcard := Finset.card_erase_add_one hb
  have hpred : B.card - 1 = (B.erase b).card := by omega
  rw [hpred]
  nlinarith

/-- The interval splits into holes, the exact block, the later residual, and the opening counter. -/
theorem residual_partition
    (N w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N) (hB : B ⊆ S)
    (hw : w ∈ S \ B) :
    (Icc 1 N \ S).card + B.card + ((S \ B).erase w).card + 1 = N := by
  have hfull := Finset.card_sdiff_add_card_eq_card hS
  have hblock := Finset.card_sdiff_add_card_eq_card hB
  have hopen := Finset.card_erase_add_one hw
  simp only [Nat.card_Icc] at hfull
  omega

/-- Density makes the number of holes no larger than the block and residual together. -/
theorem holes_le_block_add_residual
    (N d w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N) (hB : B ⊆ S)
    (hw : w ∈ S \ B) (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N) :
    (Icc 1 N \ S).card ≤ B.card + ((S \ B).erase w).card := by
  have hpart := residual_partition N w S B hS hB hw
  omega

/-- A near-deficit block in a dense position satisfies a quadratic bound in residual size. -/
theorem block_residual_mass_bound
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (hB : B ⊆ S) (hsum : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hnear : d - (Icc 1 N \ S).card ≤ b) (hw : w ∈ S \ B) :
    B.card * B.card ≤ 3 * B.card + 2 * ((S \ B).erase w).card := by
  have hcap := exact_block_card_bound N (Icc 1 N \ S).card d b S B hS hB hsum hb hnear
  have hholes := holes_le_block_add_residual N d w S B hS hB hw hlarge hdN
  have hpos : 0 < B.card := Finset.card_pos.mpr ⟨b, hb⟩
  have hpred : B.card - 1 + 1 = B.card := by omega
  have hmul := congrArg (fun n : ℕ ↦ B.card * n) hpred
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  nlinarith

private theorem block_le_four_of_residual_le_four
    (k c : ℕ) (hmass : k * k ≤ 3 * k + 2 * c) (hc : c ≤ 4) : k ≤ 4 := by
  by_contra hk
  have hk5 : 5 ≤ k := by omega
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hk5
  rw [hq] at hmass
  nlinarith

private theorem block_le_three_of_residual_le_one
    (k c : ℕ) (hmass : k * k ≤ 3 * k + 2 * c) (hc : c ≤ 1) : k ≤ 3 := by
  by_contra hk
  have hk4 : 4 ≤ k := by omega
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hk4
  rw [hq] at hmass
  nlinarith

/-- Residual size at most four bounds the exact block and the ambient interval uniformly. -/
theorem small_residual_bound
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (hB : B ⊆ S) (hsum : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hnear : d - (Icc 1 N \ S).card ≤ b) (hw : w ∈ S \ B)
    (hc : ((S \ B).erase w).card ≤ 4) :
    B.card ≤ 4 ∧ N ≤ 2 * ((S \ B).erase w).card + 9 := by
  have hmass := block_residual_mass_bound N d b w S B hS hlarge hdN hB hsum hb hnear hw
  have hk := block_le_four_of_residual_le_four B.card ((S \ B).erase w).card hmass hc
  have hholes := holes_le_block_add_residual N d w S B hS hB hw hlarge hdN
  have hpart := residual_partition N w S B hS hB hw
  exact ⟨hk, by omega⟩

/-- Explicit ambient cutoffs for residual sizes four, three, two, and one. -/
theorem small_residual_cutoffs
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (hB : B ⊆ S) (hsum : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hnear : d - (Icc 1 N \ S).card ≤ b) (hw : w ∈ S \ B) :
    (((S \ B).erase w).card ≤ 4 → B.card ≤ 4 ∧ N ≤ 17) ∧
    (((S \ B).erase w).card ≤ 3 → N ≤ 15) ∧
    (((S \ B).erase w).card ≤ 2 → N ≤ 13) ∧
    (((S \ B).erase w).card ≤ 1 → B.card ≤ 3 ∧ N ≤ 9) := by
  have hsmall := small_residual_bound N d b w S B hS hlarge hdN hB hsum hb hnear hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc
    obtain ⟨hk, hN⟩ := hsmall hc
    exact ⟨hk, by omega⟩
  · intro hc
    have hN := (hsmall (by omega)).2
    omega
  · intro hc
    have hN := (hsmall (by omega)).2
    omega
  · intro hc
    have hmass := block_residual_mass_bound N d b w S B hS hlarge hdN hB hsum hb hnear hw
    have hk := block_le_three_of_residual_le_one B.card ((S \ B).erase w).card hmass hc
    have hholes := holes_le_block_add_residual N d w S B hS hB hw hlarge hdN
    have hpart := residual_partition N w S B hS hB hw
    exact ⟨hk, by omega⟩

end CatchUp.DenseBlockMass
