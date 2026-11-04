/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseLossFrontier.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.DenseThreeResidual
public import CatchUp.DenseGapMassGeneral

/-!
# Necessary obstructions extracted from a dense loss

The maximal-block selection preserves the actual residual opening in the lower branch.
The finite residual closure and uniform gap mass bound then restrict every hypothetical
dense loss to an upper descent or a nonterminal lower obstruction of residual size at least four.
The witness record contains only arithmetic data; outcome assertions remain theorem conclusions.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseLossFrontier

open CatchUp (Position.loss_after_continuing_pick)

/-- Arithmetic data of the selected maximal exact-block lower branch.
This is a necessary witness package, with no game-value predicate or invariance claim. -/
structure LowerGeometry (N d : ℕ) (S : Finset ℕ) where
  block : Finset ℕ
  maxMember : ℕ
  opening : ℕ
  block_subset : block ⊆ S
  block_sum : block.sum (fun x ↦ x) = d
  max_mem : maxMember ∈ block
  global_max : ∀ A : Finset ℕ, A ⊆ S → A.sum (fun x ↦ x) = d →
    ∀ x ∈ A, x ≤ maxMember
  max_near : d - (Icc 1 N \ S).card ≤ maxMember
  block_card : block.card ≤ (Icc 1 N \ S).card + 1
  opening_mem : opening ∈ S \ block
  max_lt_opening : maxMember < opening
  opening_lt_deficit : opening < d
  gap_positive : 1 ≤ d - opening
  gap_lt_holes : d - opening < (Icc 1 N \ S).card
  subsum_gap : ∀ A : Finset ℕ, A ⊆ S → A.sum (fun x ↦ x) ≠ d - opening

private theorem selected_loss_dichotomy
    (N d : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    (∃ B : Finset ℕ, B.Nonempty ∧ B ⊆ S ∧ B.card ≤ (Icc 1 N \ S).card + 1 ∧
      B.sum (fun x ↦ x) = d ∧ ∃ w ∈ S \ B,
        d < w ∧ (afterOpening (S \ B) w).value = .loss) ∨
    (∃ q : LowerGeometry N d S,
      (afterOpening (S \ q.block) q.opening).value = .loss ∧
      (⟨S.erase q.opening, d - q.opening⟩ : Position).value = .loss) := by
  classical
  let h := (Icc 1 N \ S).card
  let T := S.filter (fun b ↦ ∃ B : Finset ℕ,
    B ⊆ S ∧ B.sum (fun x ↦ x) = d ∧ b ∈ B)
  obtain ⟨A, hAS, hsumA, a, haA, ha⟩ :=
    DenseLossSubsumGap.exists_large_exact_block_member N h d S hS le_rfl hlarge hdN
  have haT : a ∈ T := mem_filter.mpr ⟨hAS haA, A, hAS, hsumA, haA⟩
  have hT : T.Nonempty := ⟨a, haT⟩
  let b := T.max' hT
  have hbT : b ∈ T := max'_mem T hT
  obtain ⟨_, B, hBS, hsumB, hbB⟩ := mem_filter.mp hbT
  have hB : B.Nonempty := ⟨b, hbB⟩
  have hmax (C : Finset ℕ) (hCS : C ⊆ S) (hsumC : C.sum (fun x ↦ x) = d)
      (c : ℕ) (hcC : c ∈ C) : c ≤ b := by
    apply le_max' T c
    exact mem_filter.mpr ⟨hCS hcC, C, hCS, hsumC, hcC⟩
  have hnear : d - h ≤ b := le_trans ha (le_max' T a haT)
  have hbmax : B.max' hB = b :=
    le_antisymm (hmax B hBS hsumB _ (max'_mem B hB)) (le_max' B b hbB)
  have hsumErase : (B.erase b).sum (fun x ↦ x) + b = d := by
    simpa only [hsumB] using sum_erase_add B (fun x : ℕ ↦ x) hbB
  have hcardErase : (B.erase b).card ≤ (B.erase b).sum (fun x ↦ x) := by
    calc
      (B.erase b).card = (B.erase b).sum (fun _ ↦ 1) := by simp
      _ ≤ (B.erase b).sum (fun x ↦ x) := sum_le_sum (fun x hx ↦
        (mem_Icc.mp (hS (hBS (mem_of_mem_erase hx)))).1)
  have hcardB : B.card ≤ h + 1 := by
    have hc := card_erase_add_one hbB
    omega
  obtain ⟨w, hw, hresloss, hbw⟩ :=
    Position.exists_winning_opening_gt_max_of_loss_of_exact_sum S B d hB
      (by intro x hx; exact (mem_Icc.mp (hS (hBS hx))).1) hBS hsumB hloss
  rw [hbmax] at hbw
  by_cases hdw : d < w
  · exact Or.inl ⟨B, hB, hBS, hcardB, hsumB, w, hw, hdw, hresloss⟩
  · have hwS : w ∈ S := (mem_sdiff.mp hw).1
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
    have hgap (C : Finset ℕ) (hCS : C ⊆ S) : C.sum (fun x ↦ x) ≠ d - w := by
      intro hsumC
      have hwC : w ∉ C := by
        intro hmem
        have hc := single_le_sum (fun x _ ↦ Nat.zero_le x) hmem
        change w ≤ C.sum (fun x ↦ x) at hc
        omega
      have hsub : insert w C ⊆ S := by
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact hwS
        · exact hCS hx
      have hsum : (insert w C).sum (fun x ↦ x) = d := by
        rw [sum_insert hwC, hsumC]
        omega
      have hwb := hmax (insert w C) hsub hsum w (by simp)
      omega
    have hcatch : ¬ S.sum (fun x ↦ x) < d := by
      have hc := sum_le_sum_of_subset (f := fun x : ℕ ↦ x) hBS
      try simp only at hc
      rw [hsumB] at hc
      omega
    have hchild := Position.loss_after_continuing_pick (⟨S, d⟩ : Position)
      hwS hcatch hwd hloss
    let q : LowerGeometry N d S :=
      { block := B, maxMember := b, opening := w, block_subset := hBS,
        block_sum := hsumB, max_mem := hbB, global_max := hmax, max_near := hnear,
        block_card := hcardB, opening_mem := hw, max_lt_opening := hbw,
        opening_lt_deficit := hwd, gap_positive := htpos, gap_lt_holes := hth,
        subsum_gap := hgap }
    right
    refine ⟨q, hresloss, ?_⟩
    simpa [q, Position.afterPick, hwd] using hchild

/-- Every hypothetical even dense loss has an upper descent, or a fully witnessed lower loss
whose actual residual is nonterminal, has at least four counters, and obeys the uniform gap mass
bound. Neither alternative asserts preservation of density in a successor. -/
theorem loss_frontier
    (N d : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (heven : Even (S.sum (fun x ↦ x) + d))
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    (∃ B : Finset ℕ, B.Nonempty ∧ B ⊆ S ∧ B.card ≤ (Icc 1 N \ S).card + 1 ∧
      B.sum (fun x ↦ x) = d ∧ ∃ w ∈ S \ B,
        d < w ∧ (afterOpening (S \ B) w).value = .loss) ∨
    (∃ q : LowerGeometry N d S,
      (afterOpening (S \ q.block) q.opening).value = .loss ∧
      (⟨S.erase q.opening, d - q.opening⟩ : Position).value = .loss ∧
      CatchUp.value (S \ q.block) = .win ∧
      q.opening ≤ ((S \ q.block).erase q.opening).sum (fun x ↦ x) ∧
      4 ≤ ((S \ q.block).erase q.opening).card ∧
      q.block.card * (q.block.card - 1) ≤
        2 * ((S \ q.block).erase q.opening).card + 4) := by
  rcases selected_loss_dichotomy N d S hS hlarge hdN hloss with hupper | hlower
  · exact Or.inl hupper
  · obtain ⟨q, hresloss, hchildloss⟩ := hlower
    have hreswin : CatchUp.value (S \ q.block) = .win :=
      (value_eq_win_iff_exists_winning_opening (S \ q.block)
        ⟨q.opening, q.opening_mem⟩).mpr ⟨q.opening, q.opening_mem, hresloss⟩
    have hcatch : q.opening ≤ ((S \ q.block).erase q.opening).sum (fun x ↦ x) := by
      by_contra hnot
      have hnonloss := DenseTerminalNonloss.terminal_gap_successor_nonloss N d q.opening
        S q.block hS hlarge hdN heven q.block_subset q.block_sum q.opening_mem
        q.opening_lt_deficit q.gap_lt_holes q.subsum_gap (by omega)
      exact hnonloss hchildloss
    have hfour : 4 ≤ ((S \ q.block).erase q.opening).card := by
      by_contra hnot
      have hnonloss := DenseThreeResidual.small_residual_successor_nonloss
        N d q.maxMember q.opening S q.block hS hlarge hdN heven q.block_subset
        q.block_sum q.max_mem q.global_max q.opening_mem q.max_lt_opening
        q.opening_lt_deficit q.subsum_gap (by omega) hresloss
      exact hnonloss hchildloss
    have hmass := DenseGapMassGeneral.block_card_bound N d q.maxMember q.opening S q.block
      hS hlarge hdN q.block_subset q.block_sum q.max_mem q.max_near q.opening_mem
      q.max_lt_opening q.opening_lt_deficit q.subsum_gap
    exact Or.inr ⟨q, hresloss, hchildloss, hreswin, hcatch, hfour, hmass⟩

end CatchUp.DenseLossFrontier
