/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseLossSubsumGap.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.DenseLossGeneral

/-!
# Maximal exact blocks expose true subset-sum gaps

A dense losing state either descends to a higher losing deficit after a bounded-size exact block,
or one compulsory continuing pick exposes a small deficit unrepresentable by any subset of the
original support. No preservation of the density or subsum hypotheses is asserted.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseLossSubsumGap

open CatchUp (Position.loss_after_continuing_pick)

/-- An exact-deficit block contains a counter at least d minus the hole budget. -/
theorem exists_large_exact_block_member
    (N h d : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hholes : (Icc 1 N \ S).card ≤ h) (hlarge : 2 * h + 1 ≤ d) (hdN : d ≤ N) :
    ∃ B : Finset ℕ, B ⊆ S ∧ B.sum (fun x ↦ x) = d ∧
      ∃ b ∈ B, d - h ≤ b := by
  classical
  by_cases hdS : d ∈ S
  · exact ⟨{d}, by simpa using hdS, by simp, d, by simp, by omega⟩
  · obtain ⟨i, hipos, hih, hiS, hdiS⟩ :=
      DenseLossGeneral.exists_small_complement_pair N h d S hS hholes hlarge hdN hdS
    have hlt : i < d - i := by omega
    refine ⟨{i, d - i}, ?_, ?_, d - i, by simp, by omega⟩
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hiS
      · exact hdiS
    · simp [ne_of_lt hlt]
      omega

/-- A dense loss has a bounded upper descent or a small deficit with no subset representation. -/
theorem loss_dichotomy
    (N h d : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hholes : (Icc 1 N \ S).card ≤ h) (hlarge : 2 * h + 1 ≤ d) (hdN : d ≤ N)
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    (∃ B : Finset ℕ, B.Nonempty ∧ B ⊆ S ∧ B.card ≤ h + 1 ∧
      B.sum (fun x ↦ x) = d ∧ ∃ w ∈ S \ B,
        d < w ∧ (afterOpening (S \ B) w).value = .loss) ∨
    (∃ t, 1 ≤ t ∧ t < h ∧
      (∀ A : Finset ℕ, A ⊆ S → A.sum (fun x ↦ x) ≠ t) ∧ d - t ∈ S ∧
      (⟨S.erase (d - t), t⟩ : Position).value = .loss) := by
  classical
  let T := S.filter (fun b ↦ ∃ B : Finset ℕ,
    B ⊆ S ∧ B.sum (fun x ↦ x) = d ∧ b ∈ B)
  obtain ⟨A, hAS, hsumA, a, haA, ha⟩ :=
    exists_large_exact_block_member N h d S hS hholes hlarge hdN
  have haT : a ∈ T := mem_filter.mpr ⟨hAS haA, A, hAS, hsumA, haA⟩
  have hT : T.Nonempty := ⟨a, haT⟩
  let b := T.max' hT
  have hbT : b ∈ T := Finset.max'_mem T hT
  obtain ⟨hbS, B, hBS, hsumB, hbB⟩ := mem_filter.mp hbT
  have hB : B.Nonempty := ⟨b, hbB⟩
  have hmax (C : Finset ℕ) (hCS : C ⊆ S) (hsumC : C.sum (fun x ↦ x) = d)
      (c : ℕ) (hcC : c ∈ C) : c ≤ b := by
    apply Finset.le_max' T c
    exact mem_filter.mpr ⟨hCS hcC, C, hCS, hsumC, hcC⟩
  have hblarge : d - h ≤ b := le_trans ha (Finset.le_max' T a haT)
  have hbmax : B.max' hB = b :=
    le_antisymm (hmax B hBS hsumB _ (Finset.max'_mem B hB))
      (Finset.le_max' B b hbB)
  have hsumErase : (B.erase b).sum (fun x ↦ x) + b = d := by
    simpa only [hsumB] using Finset.sum_erase_add B (fun x : ℕ ↦ x) hbB
  have hcardErase : (B.erase b).card ≤ (B.erase b).sum (fun x ↦ x) := by
    calc
      (B.erase b).card = (B.erase b).sum (fun _ ↦ 1) := by simp
      _ ≤ (B.erase b).sum (fun x ↦ x) := Finset.sum_le_sum (fun x hx ↦
        (mem_Icc.mp (hS (hBS (Finset.mem_of_mem_erase hx)))).1)
  have hcardB : B.card ≤ h + 1 := by
    have hc := Finset.card_erase_add_one hbB
    omega
  obtain ⟨w, hw, hwin, hgt⟩ :=
    Position.exists_winning_opening_gt_max_of_loss_of_exact_sum S B d hB
      (by intro x hx; exact (mem_Icc.mp (hS (hBS hx))).1) hBS hsumB hloss
  rw [hbmax] at hgt
  by_cases hdw : d < w
  · exact Or.inl ⟨B, hB, hBS, hcardB, hsumB, w, hw, hdw, hwin⟩
  · right
    have hwS : w ∈ S := (mem_sdiff.mp hw).1
    have hwd : w < d := by
      have hne : w ≠ d := by
        intro he
        have hsingleton : ({w} : Finset ℕ).sum (fun x ↦ x) = d := by simp [he]
        have hwb := hmax {w} (by simpa using hwS) hsingleton w (by simp)
        omega
      omega
    have htpos : 1 ≤ d - w := by omega
    have hth : d - w < h := by omega
    have hwt : d - w < w := by omega
    have hwback : d - (d - w) = w := by omega
    have hgap (C : Finset ℕ) (hCS : C ⊆ S) : C.sum (fun x ↦ x) ≠ d - w := by
      intro hsumC
      have hwC : w ∉ C := by
        intro hmem
        have hc := Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hmem
        change w ≤ C.sum (fun x ↦ x) at hc
        omega
      have hsub : insert w C ⊆ S := by
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact hwS
        · exact hCS hx
      have hsum : (insert w C).sum (fun x ↦ x) = d := by
        rw [Finset.sum_insert hwC, hsumC]
        omega
      have hwb := hmax (insert w C) hsub hsum w (by simp)
      omega
    have hcatch : ¬ S.sum (fun x ↦ x) < d := by
      have hc := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x) hBS
      try simp only at hc
      rw [hsumB] at hc
      omega
    have hl := Position.loss_after_continuing_pick (⟨S, d⟩ : Position)
      hwS hcatch hwd hloss
    refine ⟨d - w, htpos, hth, hgap, ?_, ?_⟩
    · simpa only [hwback] using hwS
    · simpa [Position.afterPick, hwd, hwback] using hl

/-- Low-subsum coverage removes the gap branch, leaving a strictly higher losing deficit. -/
theorem upper_loss_of_low_subsum_coverage
    (N h d : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hholes : (Icc 1 N \ S).card ≤ h) (hlarge : 2 * h + 1 ≤ d) (hdN : d ≤ N)
    (hcoverage : ∀ t, 1 ≤ t → t < h → ∃ A : Finset ℕ,
      A ⊆ S ∧ A.sum (fun x ↦ x) = t)
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    ∃ B : Finset ℕ, B.Nonempty ∧ B ⊆ S ∧ B.card ≤ h + 1 ∧
      B.sum (fun x ↦ x) = d ∧ ∃ w ∈ S \ B,
        d < w ∧ (afterOpening (S \ B) w).value = .loss := by
  rcases loss_dichotomy N h d S hS hholes hlarge hdN hloss with hupper | hgap
  · exact hupper
  · obtain ⟨t, htpos, hth, hgap, _, _⟩ := hgap
    obtain ⟨A, hAS, hsumA⟩ := hcoverage t htpos hth
    exact (hgap A hAS hsumA).elim

end CatchUp.DenseLossSubsumGap
