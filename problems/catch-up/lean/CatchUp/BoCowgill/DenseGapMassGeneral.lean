/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseGapMassGeneral.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.IncompleteSubsumMass
public import CatchUp.BoCowgill.DenseBlockMass

/-! # A true subset-sum gap bounds exact-block mass for arbitrary residual sizes -/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseGapMassGeneral

/-- The missing target strengthens the exact-block cardinality bound without a residual-size cutoff. -/
theorem block_card_bound
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (hB : B ⊆ S) (hsumB : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hnear : d - (Icc 1 N \ S).card ≤ b) (hw : w ∈ S \ B)
    (hbw : b < w) (hwd : w < d)
    (hgap : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) ≠ d - w) :
    B.card * (B.card - 1) ≤ 2 * ((S \ B).erase w).card + 4 := by
  let A := B.erase b
  have hAS : A ⊆ S := fun _ hx ↦ hB (mem_of_mem_erase hx)
  have hpos : ∀ x ∈ A, 0 < x := fun x hx ↦ (mem_Icc.mp (hS (hAS hx))).1
  have hsumA : A.sum id + b = d := (Finset.sum_erase_add B (fun x : ℕ ↦ x) hb).trans hsumB
  have hcardA : A.card + 1 = B.card := Finset.card_erase_add_one hb
  have hholes := DenseBlockMass.holes_le_block_add_residual N d w S B hS hB hw hlarge hdN
  have hsmall : A.sum id ≤ A.card + ((S \ B).erase w).card + 1 := by omega
  have ht : d - w ≤ A.sum id := by omega
  have hgapA : ∀ D : Finset ℕ, D ⊆ A → D.sum id ≠ d - w := fun D hDA ↦ hgap D (fun _ hx ↦ hAS (hDA hx))
  have hbound := IncompleteSubsumMass.missing_target_card_bound A hpos (d - w) ((S \ B).erase w).card ht hgapA hsmall
  have hpred : B.card - 1 = A.card := by omega
  rw [hpred, ← hcardA]
  simpa only [Nat.mul_comm] using hbound

end CatchUp.DenseGapMassGeneral

