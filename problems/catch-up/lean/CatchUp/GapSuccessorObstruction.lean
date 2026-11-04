/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/GapSuccessorObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.ExactSumLossObstruction
public import CatchUp.Executable

/-!
# A dense even ancestor with an unsafe maximal-block gap successor

This is a counterexample to a proposed gap-preservation implication, not to the
Catch-Up conjecture or to dense high-deficit nonloss. The ancestor itself wins.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.GapSuccessorObstruction

open Finset
open CatchUp (Position.move_outcome_eq_loss_of_value_eq_loss)

def support : Finset ℕ := {4, 5, 8, 9, 10, 11, 12}
def residual : Finset ℕ := {4, 5, 8, 9, 11, 12}
def exactBlocks : Finset (Finset ℕ) := support.powerset.filter (fun B ↦ B.sum id = 13)

theorem ancestor_arithmetic :
    support ⊆ Icc 1 13 ∧ (Icc 1 13 \ support).card = 6 ∧
    2 * 6 + 1 = (13 : ℕ) ∧ Even (support.sum id + 13) ∧
    10 ∈ support ∧ 13 ∉ support ∧ 13 - 3 = (10 : ℕ) ∧ 1 ≤ (3 : ℕ) ∧ 3 < (6 : ℕ) := by
  decide +kernel

theorem exact_blocks : exactBlocks = {{4, 9}, {5, 8}} := by
  decide +kernel

theorem exact_block_cases (B : Finset ℕ) (hB : B ⊆ support) (hsum : B.sum id = 13) :
    B = {4, 9} ∨ B = {5, 8} := by
  have hm : B ∈ exactBlocks := mem_filter.mpr ⟨mem_powerset.mpr hB, hsum⟩
  rw [exact_blocks] at hm
  simpa only [mem_insert, mem_singleton] using hm

theorem exact_block_bounded (B : Finset ℕ) (hB : B ⊆ support) (hsum : B.sum id = 13) :
    B ⊆ Icc 1 9 := by
  rcases exact_block_cases B hB hsum with rfl | rfl <;> decide +kernel

theorem attained_block_bound :
    ({4, 9} : Finset ℕ) ⊆ support ∧ ({4, 9} : Finset ℕ).sum id = 13 ∧
    9 ∈ ({4, 9} : Finset ℕ) ∧ 9 < (10 : ℕ) := by
  decide +kernel

theorem no_gap_subsum : support.powerset.filter (fun B ↦ B.sum id = 3) = ∅ := by
  decide +kernel

theorem gap_unrepresentable (B : Finset ℕ) (hB : B ⊆ support) : B.sum id ≠ 3 := by
  intro hsum
  have hm : B ∈ support.powerset.filter (fun A ↦ A.sum id = 3) :=
    mem_filter.mpr ⟨mem_powerset.mpr hB, hsum⟩
  rw [no_gap_subsum] at hm
  simp at hm

theorem successor_eq : (⟨support, 13⟩ : Position).afterPick 10 = ⟨residual, 3⟩ := by
  decide +kernel

theorem residual_loss : (⟨residual, 3⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

theorem every_residual_pick_loses (x : ℕ) (hx : x ∈ residual) :
    (⟨residual, 3⟩ : Position).moveOutcome x = .loss := by
  exact Position.move_outcome_eq_loss_of_value_eq_loss _ hx (by decide +kernel) residual_loss

theorem continuing_pick_loses : (⟨support, 13⟩ : Position).moveOutcome 10 = .loss := by
  change (if 10 < 13 then ((⟨support, 13⟩ : Position).afterPick 10).value
    else ((⟨support, 13⟩ : Position).afterPick 10).value.neg) = .loss
  rw [ite_eq_left (by decide), successor_eq]
  exact residual_loss

theorem ancestor_win : (⟨support, 13⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

/-- Even a qualifying dense ancestor and a truly maximal exact block do not make its gap pick safe.
The gap pick continues the same turn and loses, although other choices win at the ancestor. -/
theorem dense_even_maximal_gap_counterexample :
    support ⊆ Icc 1 13 ∧ (Icc 1 13 \ support).card = 6 ∧
    2 * 6 + 1 ≤ (13 : ℕ) ∧ Even (support.sum id + 13) ∧
    1 ≤ (3 : ℕ) ∧ 3 < (6 : ℕ) ∧ 13 - 3 = (10 : ℕ) ∧
    10 ∈ support ∧ 13 ∉ support ∧ 10 < (13 : ℕ) ∧
    (∀ B : Finset ℕ, B ⊆ support → B.sum id = 13 → B ⊆ Icc 1 9) ∧
    (({4, 9} : Finset ℕ) ⊆ support ∧ ({4, 9} : Finset ℕ).sum id = 13 ∧
      9 ∈ ({4, 9} : Finset ℕ) ∧ 9 < (10 : ℕ)) ∧
    (∀ B : Finset ℕ, B ⊆ support → B.sum id ≠ 3) ∧
    (⟨support, 13⟩ : Position).afterPick 10 = ⟨residual, 3⟩ ∧
    ((⟨support, 13⟩ : Position).afterPick 10).value = .loss ∧
    (⟨support, 13⟩ : Position).value = .win := by
  rcases ancestor_arithmetic with ⟨hsub, hholes, hlarge, heven, hw, hd, ht, htpos, hth⟩
  exact ⟨hsub, hholes, hlarge.le, heven, htpos, hth, ht, hw, hd, by decide,
    exact_block_bounded, attained_block_bound, gap_unrepresentable, successor_eq,
    by rw [successor_eq]; exact residual_loss, ancestor_win⟩

end CatchUp.GapSuccessorObstruction
