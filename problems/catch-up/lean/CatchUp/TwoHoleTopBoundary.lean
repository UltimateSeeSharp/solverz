/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/TwoHoleTopBoundary.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.DenseLossGeneral

/-!
# Repackaging the two-hole exact-deficit boundary

The existing exact-block and opening APIs reduce any loss here to one exceptional support and a
winning smaller interval opening. This is a conditional boundary reduction, not a density closure.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.TwoHoleTopBoundary

open CatchUp (Position.loss_after_continuing_pick)

/-- Missing both endpoints exhausts a two-hole budget. -/
theorem support_eq_of_missing_endpoints
    (d : ℕ) (S : Finset ℕ) (hd : 2 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 2) (hone : 1 ∉ S) (htop : d ∉ S) :
    S = Icc 2 (d - 1) := by
  have hbase : ({1, d} : Finset ℕ) ⊆ Icc 1 d \ S := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨le_rfl, by omega⟩, hone⟩
    · exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, le_rfl⟩, htop⟩
  have hcard : ({1, d} : Finset ℕ).card = 2 := by simp [show 1 ≠ d by omega]
  have he : Icc 1 d \ S = {1, d} :=
    (Finset.eq_of_subset_of_card_le hbase (by simpa only [hcard] using hholes)).symm
  ext x
  constructor
  · intro hx
    have hp := mem_Icc.mp (hS hx)
    have hne1 : x ≠ 1 := by intro h; subst x; exact hone hx
    have hned : x ≠ d := by intro h; subst x; exact htop hx
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro hx
    have hp := mem_Icc.mp hx
    by_contra hxS
    have hh : x ∈ Icc 1 d \ S :=
      mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hxS⟩
    rw [he] at hh
    simp only [mem_insert, mem_singleton] at hh
    omega

/-- Every loss with at most two holes has the exceptional support and a losing smaller opening. -/
theorem loss_forces_exceptional_opening
    (d : ℕ) (S : Finset ℕ) (hd : 5 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 2)
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    S = Icc 2 (d - 1) ∧ (afterOpening (Icc 1 (d - 2)) 1).value = .loss := by
  have hone : 1 ∉ S := by
    intro hmem
    apply DenseLossGeneral.exact_deficit_nonloss 2 d S hS hholes (by omega) _ hloss
    intro x hx
    have he : x = 1 := by simpa using hx
    simpa only [he] using hmem
  have htop : d ∉ S := by
    intro hmem
    apply Position.value_ne_loss_of_exact_sum_block_dominates S {d} d (by simp)
      (by intro x hx; simp only [mem_singleton] at hx; subst x; omega)
      (by simpa using hmem) (by simp) _ hloss
    intro x hx
    simpa using (mem_Icc.mp (hS (mem_sdiff.mp hx).1)).2
  have heS := support_eq_of_missing_endpoints d S (by omega) hS hholes hone htop
  have hpair : ({2, d - 1} : Finset ℕ) ⊆ S := by
    rw [heS]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcatch : ¬ S.sum (fun x ↦ x) < d := by
    have hs := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x) hpair
    simp [show 2 ≠ d - 1 by omega] at hs
    omega
  have hlast : d - 1 ∈ S := by rw [heS]; exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcontinue : d - 1 < d := by omega
  have hl := Position.loss_after_continuing_pick (⟨S, d⟩ : Position)
    hlast hcatch hcontinue hloss
  have herase : S.erase (d - 1) = (Icc 1 (d - 2)).erase 1 := by
    rw [heS]
    ext x
    simp only [mem_erase, mem_Icc]
    omega
  have hchild : (⟨S, d⟩ : Position).afterPick (d - 1) =
      afterOpening (Icc 1 (d - 2)) 1 := by
    simp [Position.afterPick, afterOpening, hcontinue, herase, show d - (d - 1) = 1 by omega]
  exact ⟨heS, by simpa only [hchild] using hl⟩

/-- A loss in this boundary family forces a win on the smaller complete interval. -/
theorem loss_forces_smaller_win
    (d : ℕ) (S : Finset ℕ) (hd : 5 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 2)
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    S = Icc 2 (d - 1) ∧ value (Icc 1 (d - 2)) = .win := by
  obtain ⟨heS, hopen⟩ := loss_forces_exceptional_opening d S hd hS hholes hloss
  refine ⟨heS, ?_⟩
  apply (value_eq_win_iff_exists_winning_opening _ (by exact ⟨1, by simp; omega⟩)).2
  exact ⟨1, by simp; omega, hopen⟩

/-- Nonwinning of the smaller interval rules out loss throughout the two-hole boundary family. -/
theorem nonloss_of_smaller_nonwin
    (d : ℕ) (S : Finset ℕ) (hd : 5 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 2)
    (hsmaller : value (Icc 1 (d - 2)) ≠ .win) :
    (⟨S, d⟩ : Position).value ≠ .loss := by
  intro hloss
  exact hsmaller (loss_forces_smaller_win d S hd hS hholes hloss).2

/-- The exceptional support's effective total has the shorter triangular sum's parity. -/
theorem triangular_even_of_top_boundary (d : ℕ) (hd : 5 ≤ d)
    (he : Even ((Icc 2 (d - 1)).sum id + d)) :
    Even ((d - 2) * (d - 1) / 2) := by
  have hinterval : Ico 2 d = Icc 2 (d - 1) := by
    ext x
    simp only [mem_Ico, mem_Icc]
    omega
  have hsplit := Finset.sum_range_add_sum_Ico id (show 2 ≤ d by omega)
  rw [hinterval] at hsplit
  have hone : (Finset.range 2).sum id = 1 := by decide
  rw [hone] at hsplit
  change 1 + (Icc 2 (d - 1)).sum id = (Finset.range d).sum id at hsplit
  have hrec := Finset.sum_range_succ (f := id) (d - 1)
  rw [show d - 1 + 1 = d by omega] at hrec
  have htri := Finset.sum_range_id (d - 1)
  have hpred : d - 1 - 1 = d - 2 := by omega
  rw [hpred, Nat.mul_comm (d - 1) (d - 2)] at htri
  change (Finset.range (d - 1)).sum id = (d - 2) * (d - 1) / 2 at htri
  rw [htri] at hrec
  change (Finset.range d).sum id = (d - 2) * (d - 1) / 2 + (d - 1) at hrec
  rcases he with ⟨k, hk⟩
  refine ⟨k - (d - 1), ?_⟩
  omega

/-- An even-effective-total loss here forces an eligible smaller interval to be winning. -/
theorem loss_forces_smaller_even_win
    (d : ℕ) (S : Finset ℕ) (hd : 5 ≤ d) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ 2) (heven : Even (S.sum (fun x ↦ x) + d))
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    Even ((d - 2) * (d - 1) / 2) ∧ value (Icc 1 (d - 2)) = .win := by
  obtain ⟨heS, hwin⟩ := loss_forces_smaller_win d S hd hS hholes hloss
  refine ⟨triangular_even_of_top_boundary d hd ?_, hwin⟩
  simpa only [heS, id_eq] using heven

end CatchUp.TwoHoleTopBoundary
