/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseTerminalReduction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.TurnDepth

/-!
# Bounding an arithmetic terminal branch

This module bounds a particular exact-block terminal branch by N ≤ 9. It assumes neither a
winning-opening theorem nor maximality of the exact block, and supplies no general density closure.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseTerminalReduction

/-- The smallest possible sum of r distinct positive interval counters is triangular. -/
theorem interval_subset_sum_lower (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
    A.card * (A.card + 1) ≤ 2 * A.sum (fun x ↦ x) := by
  have hC : Icc 1 N \ A ⊆ Icc 1 N := Finset.sdiff_subset
  have htop := TurnDepth.interval_subset_sum_core N (Icc 1 N \ A) hC
  have htotal := TurnDepth.interval_sum_twice N
  have hsum := Finset.sum_sdiff (f := fun x : ℕ ↦ x) hA
  have hcard := Finset.card_sdiff_add_card_eq_card hA
  have hcardI : (Icc 1 N).card = N := by simp
  rw [hcardI] at hcard
  have hcprod := congrArg (fun n : ℕ ↦ (Icc 1 N \ A).card * (2 * n + 1)) hcard
  have hNprod := congrArg (fun n : ℕ ↦ n * (n + 1)) hcard
  nlinarith

/-- A sufficiently dense set with a small even sum is supported only below ten. -/
theorem small_even_sum_bound
    (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (hdensity : N + 1 ≤ 2 * A.card) (heven : Even (A.sum (fun x ↦ x)))
    (hsmall : A.sum (fun x ↦ x) < 2 * N) : N ≤ 9 := by
  have hmin := interval_subset_sum_lower N A hA
  by_contra hN
  have hr : 6 ≤ A.card := by omega
  rcases heven with ⟨k, hk⟩
  have hupper : A.sum (fun x ↦ x) + 2 ≤ 2 * N := by omega
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hr
  rw [hq] at hmin hdensity
  nlinarith

/-- The terminal lower branch of the dense exact-block descent has ambient size at most nine. -/
theorem terminal_branch_bound
    (N d w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (heven : Even (S.sum (fun x ↦ x) + d))
    (hB : B ⊆ S) (hsumB : B.sum (fun x ↦ x) = d)
    (hw : w ∈ S \ B) (hwd : w < d) (htmissing : d - w ∉ S)
    (hterminal : ((S \ B).erase w).sum (fun x ↦ x) < w) : N ≤ 9 := by
  classical
  let A := insert (d - w) (S.erase w)
  have hwS : w ∈ S := (mem_sdiff.mp hw).1
  have hwN := mem_Icc.mp (hS hwS)
  have htnew : d - w ∉ S.erase w := by
    intro ht
    exact htmissing (Finset.mem_of_mem_erase ht)
  have hA : A ⊆ Icc 1 N := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_Icc.mpr ⟨by omega, by omega⟩
    · exact hS (Finset.mem_of_mem_erase hx)
  have hcardA : A.card = S.card := by
    have hc := Finset.card_erase_add_one hwS
    dsimp [A]
    rw [Finset.card_insert_of_notMem htnew]
    exact hc
  have hsumA : A.sum (fun x ↦ x) = d - w + (S.erase w).sum (fun x ↦ x) := by
    exact Finset.sum_insert htnew
  have hsumS := Finset.sum_erase_add S (fun x : ℕ ↦ x) hwS
  have hsumRest := Finset.sum_sdiff (f := fun x : ℕ ↦ x) hB
  have hsumW := Finset.sum_erase_add (S \ B) (fun x : ℕ ↦ x) hw
  rw [hsumB] at hsumRest
  have heA : Even (A.sum (fun x ↦ x)) := by
    rcases heven with ⟨k, hk⟩
    refine ⟨k - w, ?_⟩
    omega
  have hsmall : A.sum (fun x ↦ x) < 2 * N := by omega
  have hcards := Finset.card_sdiff_add_card_eq_card hS
  have hdensity : N + 1 ≤ 2 * A.card := by
    rw [hcardA]
    simpa only [Nat.card_Icc] using (show N + 1 ≤ 2 * S.card by
      simp only [Nat.card_Icc] at hcards
      omega)
  exact small_even_sum_bound N A hA hdensity heA hsmall

/-- The arithmetic assumptions allow N = 9, so the uniform cutoff cannot be reduced to eight. -/
theorem cutoff_nine_witness :
    let S : Finset ℕ := {2, 3, 4, 6, 8}
    let B : Finset ℕ := {3, 6}
    S ⊆ Icc 1 9 ∧ 2 * (Icc 1 9 \ S).card + 1 ≤ 9 ∧
      Even (S.sum (fun x ↦ x) + 9) ∧ B ⊆ S ∧ B.sum (fun x ↦ x) = 9 ∧
      8 ∈ S \ B ∧ 8 < 9 ∧ 9 - 8 ∉ S ∧
      ((S \ B).erase 8).sum (fun x ↦ x) < 8 := by
  decide +kernel

end CatchUp.DenseTerminalReduction
