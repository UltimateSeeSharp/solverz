/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseTwoResidual.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DenseBlockMass
public import CatchUp.BoCowgill.DenseLossSubsumGap
public import CatchUp.BoCowgill.DenseTerminalNonloss
public import CatchUp.BoCowgill.PairClassification

/-! # Excluding a nonterminal two-counter residual in the dense subsum-gap branch -/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseTwoResidual

open CatchUp (Position.loss_after_continuing_pick)
open CatchUpSearch.TopFourClassification (value_singleton)

/-- A catchable losing two-counter state with its deficit absent has both counters above it. -/
theorem deficit_lt_each_of_pair_loss (C : Finset ℕ) (e : ℕ)
    (hcard : C.card = 2) (hcatch : e ≤ C.sum id) (habsent : e ∉ C)
    (hloss : Position.value ⟨C, e⟩ = .loss) : ∀ x ∈ C, e < x := by
  have pair_lt (x y : ℕ) (hxy : x ≠ y) (hcatch' : e ≤ x + y)
      (he : e ≠ x) (hloss' : Position.value ⟨{x, y}, e⟩ = .loss) : e < x := by
    by_contra hnot
    have hlt : x < e := by omega
    have hsum : ¬ ({x, y} : Finset ℕ).sum (fun z ↦ z) < e := by
      simp only [Finset.sum_pair hxy]
      omega
    have hchild := Position.loss_after_continuing_pick ⟨{x, y}, e⟩
      (x := x) (by simp) hsum hlt hloss'
    have hvalue : Position.value ⟨{y}, e - x⟩ = .loss := by
      simpa [Position.afterPick, hlt, hxy] using hchild
    rw [value_singleton] at hvalue
    have hle : e - x ≤ y := by omega
    by_cases heq : e - x = y
    · simp [heq] at hvalue
    · have hstrict : e - x < y := by omega
      simp [hstrict] at hvalue
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  have hs : e ≤ a + b := by simpa [hab] using hcatch
  have hea : e ≠ a := by intro he; subst e; simp at habsent
  have heb : e ≠ b := by intro he; subst e; simp at habsent
  have ha := pair_lt a b hab hs hea hloss
  have hb := pair_lt b a hab.symm (by omega) heb
    (by simpa [Finset.pair_comm] using hloss)
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb


/-- All possible small tails left after removing the largest exact-block member. -/
def tails : Finset (Finset ℕ) :=
  {∅, {1}, {2}, {3}, {4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {1, 2, 3}}

/-- The triangular mass bound leaves only ten exact-block tails. -/
theorem tail_classification :
    ∀ A ∈ (Icc 1 6).powerset, A.card ≤ 3 → A.sum (fun x ↦ x) ≤ A.card + 3 →
      A ∈ tails := by
  decide +kernel

/-- The compact arithmetic conditions after extracting the two high residual counters. -/
def finiteConfiguration (N b w u v : ℕ) (A : Finset ℕ) : Prop :=
  let B := insert b A
  let S := insert w B ∪ {u, v}
  let d := b + A.sum (fun x ↦ x)
  (∀ a ∈ A, a < b) ∧ d ≤ N ∧ 2 * (Icc 1 N \ S).card + 1 ≤ d ∧
    Even (S.sum (fun x ↦ x) + d) ∧
    (∀ D ∈ S.powerset, D.sum (fun x ↦ x) = d → ∀ x ∈ D, x ≤ b) ∧
    (∀ D ∈ S.powerset, D.sum (fun x ↦ x) ≠ d - w)

instance (N b w u v : ℕ) (A : Finset ℕ) :
    Decidable (finiteConfiguration N b w u v A) := by
  unfold finiteConfiguration
  infer_instance

/-- No even configuration survives the compact, bounded two-residual arithmetic classification. -/
theorem bounded_configuration_impossible :
    ∀ N ∈ Finset.range 14, ∀ b ∈ Icc 1 N, ∀ A ∈ tails,
      ∀ w ∈ Icc (b + 1) (b + A.sum (fun x ↦ x) - 1),
      ∀ u ∈ Icc (w + 1) N, ∀ v ∈ Icc (u + 1) N,
        ¬ finiteConfiguration N b w u v A := by
  decide +kernel

/-- A nonterminal losing two-counter residual is impossible in the dense maximal-block
gap branch. -/
theorem nonterminal_two_residual_impossible
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (heven : Even (S.sum (fun x ↦ x) + d))
    (hB : B ⊆ S) (hsumB : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hmax : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) = d → ∀ x ∈ D, x ≤ b)
    (hw : w ∈ S \ B) (hbw : b < w) (hwd : w < d)
    (hgap : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) ≠ d - w)
    (hcard : ((S \ B).erase w).card = 2)
    (hnonterminal : w ≤ ((S \ B).erase w).sum (fun x ↦ x))
    (hresloss : (afterOpening (S \ B) w).value = .loss) : False := by
  classical
  let C := (S \ B).erase w
  let A := B.erase b
  have hCS : C ⊆ S := by
    intro x hx
    exact (mem_sdiff.mp (mem_of_mem_erase hx)).1
  have hpair : ∃ u v, u < v ∧ C = {u, v} := by
    obtain ⟨u, v, huv, he⟩ := Finset.card_eq_two.mp hcard
    rcases lt_or_gt_of_ne huv with hlt | hgt
    · exact ⟨u, v, hlt, he⟩
    · exact ⟨v, u, hgt, by simpa only [Finset.pair_comm] using he⟩
  obtain ⟨u, v, huv, heC⟩ := hpair
  have heach := deficit_lt_each_of_pair_loss C w hcard hnonterminal
    (by simp [C]) hresloss
  have huC : u ∈ C := by rw [heC]; simp
  have hvC : v ∈ C := by rw [heC]; simp
  have hwu : w < u := heach u huC
  have huN := mem_Icc.mp (hS (hCS huC))
  have hvN := mem_Icc.mp (hS (hCS hvC))
  obtain ⟨D, hDS, hsumD, a, haD, ha⟩ :=
    DenseLossSubsumGap.exists_large_exact_block_member N (Icc 1 N \ S).card d S
      hS le_rfl hlarge hdN
  have hnear : d - (Icc 1 N \ S).card ≤ b := le_trans ha (hmax D hDS hsumD a haD)
  obtain ⟨hk, hNbound⟩ := DenseBlockMass.small_residual_bound N d b w S B hS hlarge hdN
    hB hsumB hb hnear hw (by omega)
  have hN : N ≤ 13 := by omega
  have hholes := DenseBlockMass.holes_le_block_add_residual N d w S B hS hB hw hlarge hdN
  have hcardA : A.card + 1 = B.card := Finset.card_erase_add_one hb
  have hsumA : A.sum (fun x ↦ x) + b = d := by
    simpa only [hsumB] using Finset.sum_erase_add B (fun x : ℕ ↦ x) hb
  have hmassA : A.sum (fun x ↦ x) ≤ A.card + 3 := by omega
  have hsmallA : A.card ≤ 3 := by omega
  have hAa : ∀ a ∈ A, a < b := by
    intro x hx
    have hle := hmax B hB hsumB x (mem_of_mem_erase hx)
    have hne := Finset.ne_of_mem_erase hx
    omega
  have hA6 : A ⊆ Icc 1 6 := by
    intro x hx
    have hp := mem_Icc.mp (hS (hB (mem_of_mem_erase hx)))
    have hs := Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hx
    change x ≤ A.sum (fun x ↦ x) at hs
    exact mem_Icc.mpr ⟨hp.1, by omega⟩
  have htail : A ∈ tails :=
    tail_classification A (mem_powerset.mpr hA6) hsmallA hmassA
  have hrest : S \ B = insert w C := (Finset.insert_erase hw).symm
  have hpart := Finset.sdiff_union_of_subset hB
  have heS : S = insert w (insert b A) ∪ {u, v} := by
    calc
      S = (S \ B) ∪ B := hpart.symm
      _ = insert w C ∪ B := by rw [hrest]
      _ = insert w (insert b A) ∪ {u, v} := by
        rw [heC]
        have heB : insert b A = B := Finset.insert_erase hb
        rw [heB]
        ext x
        simp only [mem_union, mem_insert]
        tauto
  have hed : d = b + A.sum (fun x ↦ x) := by omega
  have hconfig : finiteConfiguration N b w u v A := by
    dsimp only [finiteConfiguration]
    rw [← heS, ← hed]
    refine ⟨hAa, hdN, hlarge, heven, ?_, ?_⟩
    · intro D hD hsum x hx
      exact hmax D (mem_powerset.mp hD) hsum x hx
    · intro D hD
      exact hgap D (mem_powerset.mp hD)
  have hbN := mem_Icc.mp (hS (hB hb))
  exact bounded_configuration_impossible N (Finset.mem_range.mpr (by omega)) b
    (mem_Icc.mpr hbN) A htail w (mem_Icc.mpr ⟨by omega, by omega⟩)
    u (mem_Icc.mpr ⟨by omega, huN.2⟩) v (mem_Icc.mpr ⟨by omega, hvN.2⟩) hconfig

/-- A losing residual of size at most one must already be terminal by its total. -/
theorem sum_lt_of_loss_card_le_one (C : Finset ℕ) (e : ℕ) (hcard : C.card ≤ 1)
    (hloss : (⟨C, e⟩ : Position).value = .loss) : C.sum (fun x ↦ x) < e := by
  by_cases hzero : C.card = 0
  · have heC : C = ∅ := Finset.card_eq_zero.mp hzero
    subst C
    by_cases he : e = 0
    · simp [he, Position.value.eq_def] at hloss
    · simp only [Finset.sum_empty]
      omega
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (show C.card = 1 by omega)
    rw [value_singleton] at hloss
    simp only [Finset.sum_singleton]
    by_contra hnot
    by_cases he : e = x
    · simp [he] at hloss
    · have hstrict : e < x := by omega
      simp [hstrict] at hloss

/-- The full maximal-block gap branch has a nonlosing successor whenever its residual
has size at most two. -/
theorem small_residual_successor_nonloss
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (heven : Even (S.sum (fun x ↦ x) + d))
    (hB : B ⊆ S) (hsumB : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hmax : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) = d → ∀ x ∈ D, x ≤ b)
    (hw : w ∈ S \ B) (hbw : b < w) (hwd : w < d)
    (hgap : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) ≠ d - w)
    (hcard : ((S \ B).erase w).card ≤ 2)
    (hresloss : (afterOpening (S \ B) w).value = .loss) :
    (⟨S.erase w, d - w⟩ : Position).value ≠ .loss := by
  by_cases hterminal : ((S \ B).erase w).sum (fun x ↦ x) < w
  · obtain ⟨D, hDS, hsumD, a, haD, ha⟩ :=
      DenseLossSubsumGap.exists_large_exact_block_member N (Icc 1 N \ S).card d S
        hS le_rfl hlarge hdN
    have hnear : d - (Icc 1 N \ S).card ≤ b := le_trans ha (hmax D hDS hsumD a haD)
    have htsmall : d - w < (Icc 1 N \ S).card := by omega
    exact DenseTerminalNonloss.terminal_gap_successor_nonloss N d w S B hS hlarge hdN
      heven hB hsumB hw hwd htsmall hgap hterminal
  · by_cases htwo : ((S \ B).erase w).card = 2
    · exact (nonterminal_two_residual_impossible N d b w S B hS hlarge hdN heven hB
        hsumB hb hmax hw hbw hwd hgap htwo (by omega) hresloss).elim
    · have hone : ((S \ B).erase w).card ≤ 1 := by omega
      exact (hterminal (sum_lt_of_loss_card_le_one _ w hone hresloss)).elim

end CatchUp.DenseTwoResidual
