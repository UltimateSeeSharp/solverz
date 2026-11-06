/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ThreeHoleTopBoundary.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DenseLossGeneral

/-!
# Repackaging the three-hole top boundary with counter one present

The existing exact-block and opening APIs force any loss into one support and a winning smaller
interval opening. These conditional reductions do not close a density invariant.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.ThreeHoleTopBoundary

open CatchUp (Position.loss_after_continuing_pick)

/-- The three prescribed missing counters exhaust a three-hole budget. -/
theorem support_eq_of_three_missing
    (d : ℕ) (S : Finset ℕ) (hd : 7 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 3)
    (htwo : 2 ∉ S) (hprev : d - 1 ∉ S) (htop : d ∉ S) :
    S = (Icc 1 (d - 2)).erase 2 := by
  have hbase : ({2, d - 1, d} : Finset ℕ) ⊆ Icc 1 d \ S := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, htwo⟩
    · exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hprev⟩
    · exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, le_rfl⟩, htop⟩
  have hcard : ({2, d - 1, d} : Finset ℕ).card = 3 := by
    simp [show 2 ≠ d - 1 by omega, show 2 ≠ d by omega, show d - 1 ≠ d by omega]
  have he : Icc 1 d \ S = {2, d - 1, d} :=
    (Finset.eq_of_subset_of_card_le hbase (by simpa only [hcard] using hholes)).symm
  ext x
  constructor
  · intro hx
    have hp := mem_Icc.mp (hS hx)
    have hne2 : x ≠ 2 := by intro h; subst x; exact htwo hx
    have hnep : x ≠ d - 1 := by intro h; subst x; exact hprev hx
    have hned : x ≠ d := by intro h; subst x; exact htop hx
    exact mem_erase.mpr ⟨hne2, mem_Icc.mpr ⟨hp.1, by omega⟩⟩
  · intro hx
    have hp := mem_Icc.mp (mem_erase.mp hx).2
    have hne2 := (mem_erase.mp hx).1
    by_contra hxS
    have hh : x ∈ Icc 1 d \ S :=
      mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hp.1, by omega⟩, hxS⟩
    rw [he] at hh
    simp only [mem_insert, mem_singleton] at hh
    omega

/-- With one present, every loss at the three-hole top boundary has a losing smaller opening two. -/
theorem loss_forces_exceptional_opening
    (d : ℕ) (S : Finset ℕ) (hd : 7 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 3) (hone : 1 ∈ S)
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    S = (Icc 1 (d - 2)).erase 2 ∧
      (afterOpening (Icc 1 (d - 3)) 2).value = .loss := by
  have htwo : 2 ∉ S := by
    intro hmem
    apply DenseLossGeneral.exact_deficit_nonloss 3 d S hS hholes (by omega) _ hloss
    intro x hx
    have hp := mem_Icc.mp hx
    have he : x = 1 ∨ x = 2 := by omega
    rcases he with rfl | rfl
    · exact hone
    · exact hmem
  have htop : d ∉ S := by
    intro hmem
    apply Position.value_ne_loss_of_exact_sum_block_dominates S {d} d (by simp)
      (by intro x hx; simp only [mem_singleton] at hx; subst x; omega)
      (by simpa using hmem) (by simp) _ hloss
    intro x hx
    simpa using (mem_Icc.mp (hS (mem_sdiff.mp hx).1)).2
  have hprev : d - 1 ∉ S := by
    intro hmem
    have hB : ({1, d - 1} : Finset ℕ).Nonempty := by simp
    have hBS : ({1, d - 1} : Finset ℕ) ⊆ S := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hone
      · exact hmem
    have hsum : ({1, d - 1} : Finset ℕ).sum (fun x ↦ x) = d := by
      simp [show 1 ≠ d - 1 by omega]
      omega
    apply Position.value_ne_loss_of_exact_sum_block_dominates S {1, d - 1} d hB
      (by intro x hx; exact (mem_Icc.mp (hS (hBS hx))).1) hBS hsum _ hloss
    intro x hx
    have hp := mem_Icc.mp (hS (mem_sdiff.mp hx).1)
    have hne : x ≠ d := by intro h; subst x; exact htop (mem_sdiff.mp hx).1
    exact le_trans (show x ≤ d - 1 by omega)
      (Finset.le_max' {1, d - 1} (d - 1) (by simp))
  have heS := support_eq_of_three_missing d S hd hS hholes htwo hprev htop
  have hpair : ({3, d - 2} : Finset ℕ) ⊆ S := by
    rw [heS]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> apply mem_erase.mpr <;>
      exact ⟨by omega, mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hcatch : ¬ S.sum (fun x ↦ x) < d := by
    have hs := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x) hpair
    simp [show 3 ≠ d - 2 by omega] at hs
    omega
  have hlast : d - 2 ∈ S := hpair (by simp)
  have hcontinue : d - 2 < d := by omega
  have hl := Position.loss_after_continuing_pick (⟨S, d⟩ : Position)
    hlast hcatch hcontinue hloss
  have herase : S.erase (d - 2) = (Icc 1 (d - 3)).erase 2 := by
    rw [heS]
    ext x
    simp only [mem_erase, mem_Icc]
    omega
  have hchild : (⟨S, d⟩ : Position).afterPick (d - 2) =
      afterOpening (Icc 1 (d - 3)) 2 := by
    simp [Position.afterPick, afterOpening, hcontinue, herase, show d - (d - 2) = 2 by omega]
  exact ⟨heS, by simpa only [hchild] using hl⟩

/-- A loss in this three-hole family forces a win on the smaller complete interval. -/
theorem loss_forces_smaller_win
    (d : ℕ) (S : Finset ℕ) (hd : 7 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 3) (hone : 1 ∈ S)
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    S = (Icc 1 (d - 2)).erase 2 ∧ value (Icc 1 (d - 3)) = .win := by
  obtain ⟨heS, hopen⟩ := loss_forces_exceptional_opening d S hd hS hholes hone hloss
  refine ⟨heS, ?_⟩
  apply (value_eq_win_iff_exists_winning_opening _ (by exact ⟨2, by simp; omega⟩)).2
  exact ⟨2, by simp; omega, hopen⟩

/-- Nonwinning of the shorter interval rules out loss in the three-hole family with one present. -/
theorem nonloss_of_smaller_nonwin
    (d : ℕ) (S : Finset ℕ) (hd : 7 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 3) (hone : 1 ∈ S)
    (hsmaller : value (Icc 1 (d - 3)) ≠ .win) :
    (⟨S, d⟩ : Position).value ≠ .loss := by
  intro hloss
  exact hsmaller (loss_forces_smaller_win d S hd hS hholes hone hloss).2

/-- The exceptional three-hole support has the shorter triangular effective parity. -/
theorem triangular_even_of_top_boundary (d : ℕ) (hd : 7 ≤ d)
    (he : Even (((Icc 1 (d - 2)).erase 2).sum id + d)) :
    Even ((d - 3) * (d - 2) / 2) := by
  have hinterval : Ico 1 (d - 1) = Icc 1 (d - 2) := by
    ext x
    simp only [mem_Ico, mem_Icc]
    omega
  have hsplit := Finset.sum_range_add_sum_Ico id (show 1 ≤ d - 1 by omega)
  rw [hinterval] at hsplit
  have hzero : (Finset.range 1).sum id = 0 := by decide
  rw [hzero, zero_add] at hsplit
  change (Icc 1 (d - 2)).sum id = (Finset.range (d - 1)).sum id at hsplit
  have herase := Finset.sum_erase_add (Icc 1 (d - 2)) id
    (show 2 ∈ Icc 1 (d - 2) by simp; omega)
  change ((Icc 1 (d - 2)).erase 2).sum id + 2 = (Icc 1 (d - 2)).sum id at herase
  have hrec := Finset.sum_range_succ (f := id) (d - 2)
  rw [show d - 2 + 1 = d - 1 by omega] at hrec
  have htri := Finset.sum_range_id (d - 2)
  have hpred : d - 2 - 1 = d - 3 := by omega
  rw [hpred, Nat.mul_comm (d - 2) (d - 3)] at htri
  change (Finset.range (d - 2)).sum id = (d - 3) * (d - 2) / 2 at htri
  rw [htri] at hrec
  change (Finset.range (d - 1)).sum id = (d - 3) * (d - 2) / 2 + (d - 2) at hrec
  rcases he with ⟨k, hk⟩
  refine ⟨k - (d - 2), ?_⟩
  omega

/-- An even-effective-total loss here forces an eligible smaller interval to be winning. -/
theorem loss_forces_smaller_even_win
    (d : ℕ) (S : Finset ℕ) (hd : 7 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 3) (hone : 1 ∈ S)
    (heven : Even (S.sum (fun x ↦ x) + d))
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    Even ((d - 3) * (d - 2) / 2) ∧ value (Icc 1 (d - 3)) = .win := by
  obtain ⟨heS, hwin⟩ := loss_forces_smaller_win d S hd hS hholes hone hloss
  refine ⟨triangular_even_of_top_boundary d hd ?_, hwin⟩
  simpa only [heS, id_eq] using heven

end CatchUp.ThreeHoleTopBoundary
