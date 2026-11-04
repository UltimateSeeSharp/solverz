/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/FullGapDensityObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.ExactSumLossObstruction

/-!
# Density cannot be dropped from a full strategic gap-closing claim

This sparse even losing ancestor has a genuine winning residual opening above
every exact-deficit block. The corresponding continuing gap pick still loses.
Its missing-counter budget violates the density threshold; it is not an H or C counterexample.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.FullGapDensityObstruction

open Finset
open CatchUp (Position.move_outcome_eq_loss_of_value_eq_loss)

def support : Finset ℕ := {3, 4, 7, 8}
def residual : Finset ℕ := {3, 4, 7}
def block : Finset ℕ := {3, 7}
def exactBlocks : Finset (Finset ℕ) := support.powerset.filter (fun B ↦ B.sum id = 10)

theorem ancestor_arithmetic :
    support ⊆ Icc 1 10 ∧ (Icc 1 10 \ support).card = 6 ∧
    (10 : ℕ) < 2 * 6 + 1 ∧ Even (support.sum id + 10) ∧
    8 ∈ support ∧ 10 ∉ support ∧ 10 - 2 = (8 : ℕ) ∧ 1 ≤ (2 : ℕ) ∧ 2 < (6 : ℕ) := by
  decide +kernel

theorem exact_blocks : exactBlocks = {block} := by
  decide +kernel

theorem exact_block_unique (B : Finset ℕ) (hB : B ⊆ support) (hsum : B.sum id = 10) :
    B = block := by
  have hm : B ∈ exactBlocks := mem_filter.mpr ⟨mem_powerset.mpr hB, hsum⟩
  rw [exact_blocks] at hm
  exact mem_singleton.mp hm

theorem maximal_block :
    block.Nonempty ∧ block ⊆ support ∧ block.sum id = 10 ∧ block ⊆ Icc 1 7 ∧
    7 ∈ block ∧ 7 < (8 : ℕ) := by
  decide +kernel

theorem exact_block_bounded (B : Finset ℕ) (hB : B ⊆ support) (hsum : B.sum id = 10) :
    B ⊆ Icc 1 7 := by
  rw [exact_block_unique B hB hsum]
  exact maximal_block.2.2.2.1

theorem no_gap_subsum : support.powerset.filter (fun B ↦ B.sum id = 2) = ∅ := by
  decide +kernel

theorem gap_unrepresentable (B : Finset ℕ) (hB : B ⊆ support) : B.sum id ≠ 2 := by
  intro hsum
  have hm : B ∈ support.powerset.filter (fun A ↦ A.sum id = 2) :=
    mem_filter.mpr ⟨mem_powerset.mpr hB, hsum⟩
  rw [no_gap_subsum] at hm
  simp at hm

theorem residual_opening_eq : afterOpening (support \ block) 8 = ⟨{4}, 8⟩ := by
  decide +kernel

theorem winning_residual_opening : (afterOpening (support \ block) 8).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

theorem successor_eq : (⟨support, 10⟩ : Position).afterPick 8 = ⟨residual, 2⟩ := by
  decide +kernel

theorem residual_loss : (⟨residual, 2⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

theorem every_residual_pick_loses (x : ℕ) (hx : x ∈ residual) :
    (⟨residual, 2⟩ : Position).moveOutcome x = .loss := by
  exact Position.move_outcome_eq_loss_of_value_eq_loss _ hx (by decide +kernel) residual_loss

theorem ancestor_loss : (⟨support, 10⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

theorem every_ancestor_pick_loses (x : ℕ) (hx : x ∈ support) :
    (⟨support, 10⟩ : Position).moveOutcome x = .loss := by
  exact Position.move_outcome_eq_loss_of_value_eq_loss _ hx (by decide +kernel) ancestor_loss

/-- The full strategic witness and parent loss do not make the gap successor safe without density. -/
theorem full_gap_counterexample_without_density :
    support ⊆ Icc 1 10 ∧ (Icc 1 10 \ support).card = 6 ∧
    (10 : ℕ) < 2 * 6 + 1 ∧ Even (support.sum id + 10) ∧
    (⟨support, 10⟩ : Position).value = .loss ∧
    block.Nonempty ∧ block ⊆ support ∧ block.sum id = 10 ∧
    (∀ B : Finset ℕ, B ⊆ support → B.sum id = 10 → B ⊆ Icc 1 7) ∧
    7 ∈ block ∧ 7 < (8 : ℕ) ∧ 1 ≤ (2 : ℕ) ∧ 2 < (6 : ℕ) ∧
    10 - 2 = (8 : ℕ) ∧ 8 ∈ support ∧ 8 < (10 : ℕ) ∧
    (∀ B : Finset ℕ, B ⊆ support → B.sum id ≠ 2) ∧
    (afterOpening (support \ block) 8).value = .loss ∧
    (⟨support, 10⟩ : Position).afterPick 8 = ⟨residual, 2⟩ ∧
    ((⟨support, 10⟩ : Position).afterPick 8).value = .loss := by
  rcases ancestor_arithmetic with ⟨hsub, hholes, hdensity, heven, hw, _, ht, htpos, hth⟩
  rcases maximal_block with ⟨hne, hbsub, hsum, _, hseven, hsevenw⟩
  exact ⟨hsub, hholes, hdensity, heven, ancestor_loss, hne, hbsub, hsum,
    exact_block_bounded, hseven, hsevenw, htpos, hth, ht, hw, by decide,
    gap_unrepresentable, winning_residual_opening, successor_eq,
    by rw [successor_eq]; exact residual_loss⟩

end CatchUp.FullGapDensityObstruction
