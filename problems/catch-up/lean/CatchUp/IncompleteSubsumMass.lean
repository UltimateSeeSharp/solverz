/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/IncompleteSubsumMass.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.DenseTerminalReduction
public import Mathlib.Combinatorics.Additive.SubsetSum

/-!
# Missing subset sums require extra mass

For r distinct positive counters, a missing subset sum between zero and their total
forces total mass at least r(r+1)/2+r-1. The subtraction-free theorem includes
empty and singleton sets without a cardinality hypothesis. A maximal complete prefix,
a shifted triangular bound, and elementary arithmetic give the proof.

The final cardinality corollary applies to exact-block tails in the Catch-Up density
argument. This module proves no game outcome or recursive strategic closure.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.IncompleteSubsumMass

private def Complete (A : Finset ℕ) : Prop := ∀ t, t ≤ A.sum id → t ∈ A.subsetSum

private theorem complete_empty : Complete ∅ := by
  simp [Complete, Finset.mem_subsetSum_iff]

private theorem complete_insert {A : Finset ℕ} {a : ℕ}
    (hA : Complete A) (ha : a ∉ A) (hbound : a ≤ A.sum id + 1) :
    Complete (insert a A) := by
  intro t ht
  by_cases htA : t ≤ A.sum id
  · exact Finset.subsetSum_mono (Finset.subset_insert a A) (hA t htA)
  · rw [Finset.sum_insert ha] at ht
    change t ≤ a + A.sum id at ht
    have hsub : t - a ≤ A.sum id := by omega
    obtain ⟨B, hBA, hBsum⟩ := Finset.mem_subsetSum_iff.mp (hA (t - a) hsub)
    apply Finset.mem_subsetSum_iff.mpr
    refine ⟨insert a B, Finset.insert_subset_insert a hBA, ?_⟩
    rw [Finset.sum_insert (fun hx ↦ ha (hBA hx)), hBsum]
    omega

private theorem exists_complete_prefix (A : Finset ℕ) (hnot : ¬ Complete A) :
    ∃ P ⊆ A, Complete P ∧ P ≠ A ∧
      ∀ x ∈ A \ P, P.sum id + 2 ≤ x := by
  classical
  let F := A.powerset.filter Complete
  have hF : F.Nonempty := ⟨∅, mem_filter.mpr ⟨empty_mem_powerset A, complete_empty⟩⟩
  obtain ⟨P, hPF, hMax⟩ := Finset.exists_max_image F Finset.card hF
  have hPA : P ⊆ A := mem_powerset.mp (mem_filter.mp hPF).1
  have hPC : Complete P := (mem_filter.mp hPF).2
  have hne : P ≠ A := fun he ↦ hnot (he ▸ hPC)
  refine ⟨P, hPA, hPC, hne, ?_⟩
  intro x hx
  by_contra hsmall
  have hxP : x ∉ P := (mem_sdiff.mp hx).2
  have hnew : Complete (insert x P) := complete_insert hPC hxP (by omega)
  have hnewF : insert x P ∈ F := mem_filter.mpr
    ⟨mem_powerset.mpr (Finset.insert_subset (mem_sdiff.mp hx).1 hPA), hnew⟩
  have hcard := hMax (insert x P) hnewF
  simp [Finset.card_insert_of_notMem hxP] at hcard

private theorem shifted_mass (R : Finset ℕ) (L : ℕ)
    (hlow : ∀ x ∈ R, L + 1 ≤ x) :
    R.card * (R.card + 1) + 2 * L * R.card ≤ 2 * R.sum id := by
  classical
  let D := R.image (fun x ↦ x - L)
  have hinj : Set.InjOn (fun x : ℕ ↦ x - L) ↑R := by
    intro x hx y hy hxy
    have hxlow := hlow x hx
    have hylow := hlow y hy
    change x - L = y - L at hxy
    omega
  have hD : D ⊆ Icc 1 (R.sum id) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    have hySum : y ≤ R.sum id := Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hy
    exact mem_Icc.mpr ⟨by have := hlow y hy; omega, by omega⟩
  have hcard : D.card = R.card := Finset.card_image_iff.mpr hinj
  have hsum : D.sum id + L * R.card = R.sum id := by
    rw [show D.sum id = R.sum (fun x ↦ x - L) from Finset.sum_image hinj]
    rw [Nat.mul_comm L R.card, ← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x hx ↦ Nat.sub_add_cancel (by have := hlow x hx; omega))
  have htri := DenseTerminalReduction.interval_subset_sum_lower (R.sum id) D hD
  rw [hcard] at htri
  change R.card * (R.card + 1) ≤ 2 * D.sum id at htri
  nlinarith

private theorem prefix_mass_bound (n l p q : ℕ) (hl : 1 ≤ l)
    (hp : n * (n + 1) ≤ 2 * p)
    (hq : l * (l + 1) + 2 * (p + 1) * l ≤ 2 * q) :
    (n + l) * (n + l + 1) + 2 * (n + l) ≤ 2 * (p + q) + 2 := by
  have hweighted := Nat.mul_le_mul_left (l + 1) hp
  rcases n with _ | n
  · nlinarith
  rcases n with _ | n
  · nlinarith
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hl
  have hnonneg : 0 ≤ (n + 1) * (n + (n + 2) * j) := Nat.zero_le _
  nlinarith

private theorem mass_of_incomplete (A : Finset ℕ)
    (hpos : ∀ x ∈ A, 0 < x) (hnot : ¬ Complete A) :
    A.card * (A.card + 1) + 2 * A.card ≤ 2 * A.sum id + 2 := by
  obtain ⟨P, hPA, _hPC, hne, hrest⟩ := exists_complete_prefix A hnot
  have hRpos : 1 ≤ (A \ P).card := Finset.card_pos.mpr
    (Finset.sdiff_nonempty.mpr (fun hAP ↦ hne (Finset.Subset.antisymm hPA hAP)))
  have hp := shifted_mass P 0 (fun x hx ↦ hpos x (hPA hx))
  simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at hp
  have hq := shifted_mass (A \ P) (P.sum id + 1) (by simpa [Nat.add_assoc] using hrest)
  have hmass := prefix_mass_bound P.card (A \ P).card
    (P.sum id) ((A \ P).sum id) hRpos hp hq
  have hc : P.card + (A \ P).card = A.card := by
    simpa [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hPA
  have hs : P.sum id + (A \ P).sum id = A.sum id := by
    simpa only [Nat.add_comm] using Finset.sum_sdiff (f := id) hPA
  simpa only [hc, hs] using hmass

/-- A missing target in the attainable range forces triangular mass plus r-1.
The result uses a subtraction-free form and needs no assumption that r is at least two. -/
theorem missing_target_mass (A : Finset ℕ) (hpos : ∀ x ∈ A, 0 < x)
    (t : ℕ) (ht : t ≤ A.sum id)
    (hgap : ∀ B : Finset ℕ, B ⊆ A → B.sum id ≠ t) :
    A.card * (A.card + 1) + 2 * A.card ≤ 2 * A.sum id + 2 := by
  apply mass_of_incomplete A hpos
  intro hcomplete
  obtain ⟨B, hBA, hsum⟩ := Finset.mem_subsetSum_iff.mp (hcomplete t ht)
  exact hgap B hBA hsum

/-- A true subsum gap strengthens a small-mass cardinality bound by a linear term. -/
theorem missing_target_card_bound (A : Finset ℕ) (hpos : ∀ x ∈ A, 0 < x)
    (t c : ℕ) (ht : t ≤ A.sum id)
    (hgap : ∀ B : Finset ℕ, B ⊆ A → B.sum id ≠ t)
    (hsmall : A.sum id ≤ A.card + c + 1) :
    A.card * (A.card + 1) ≤ 2 * c + 4 := by
  have hmass := missing_target_mass A hpos t ht hgap
  omega

end CatchUp.IncompleteSubsumMass
