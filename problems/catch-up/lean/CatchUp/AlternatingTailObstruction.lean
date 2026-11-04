/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/AlternatingTailObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.DeficitTwo
public import CatchUp.WinningOpening

/-!
# Alternating odd/even tails can still lose at deficit one

The generated private proof DAG shares exact W/L subpositions. Every LOSS node
covers every legal pick; every WIN node supplies one legal winning pick.
Small leaves replay the proved executable evaluator in the kernel.
This sparse alternating tail is not an interval and proves no legal reachability claim.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.AlternatingTailObstruction

open CatchUp (Position.value_eq_loss_iff_of_nonterminal)
open CatchUp.DeficitTwo (win_of_move)

private theorem node_001 : (⟨{19, 36, 37, 50, 57, 60, 99}, 4⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_002 : (⟨{7, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 7 = (⟨{19, 36, 37, 50, 57, 60, 99}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_001]
  rfl

private theorem node_003 : (⟨{4, 19, 37, 50, 57, 60, 99}, 30⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_004 : (⟨{4, 19, 36, 37, 50, 57, 60, 99}, 6⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{4, 19, 36, 37, 50, 57, 60, 99}, 6⟩ : Position).afterPick 36 = (⟨{4, 19, 37, 50, 57, 60, 99}, 30⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_003]
  rfl

private theorem node_005 : (⟨{7, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_006 : (⟨{4, 7, 36, 37, 50, 57, 60, 99}, 18⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 36, 37, 50, 57, 60, 99}, 18⟩ : Position).afterPick 4 = (⟨{7, 36, 37, 50, 57, 60, 99}, 14⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_005]
  rfl

private theorem node_007 : (⟨{4, 7, 19, 37, 57, 60, 99}, 15⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_008 : (⟨{4, 7, 19, 37, 50, 57, 60, 99}, 35⟩ : Position).value = .win := by
  apply win_of_move _ _ 50 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 37, 50, 57, 60, 99}, 35⟩ : Position).afterPick 50 = (⟨{4, 7, 19, 37, 57, 60, 99}, 15⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_007]
  rfl

private theorem node_009 : (⟨{4, 7, 19, 36, 57, 60, 99}, 14⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_010 : (⟨{4, 7, 19, 36, 50, 57, 60, 99}, 36⟩ : Position).value = .win := by
  apply win_of_move _ _ 50 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 36, 50, 57, 60, 99}, 36⟩ : Position).afterPick 50 = (⟨{4, 7, 19, 36, 57, 60, 99}, 14⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_009]
  rfl

private theorem node_011 : (⟨{7, 19, 36, 37, 57, 60, 99}, 45⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_012 : (⟨{4, 7, 19, 36, 37, 57, 60, 99}, 49⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 36, 37, 57, 60, 99}, 49⟩ : Position).afterPick 4 = (⟨{7, 19, 36, 37, 57, 60, 99}, 45⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_011]
  rfl

private theorem node_013 : (⟨{7, 19, 36, 37, 50, 60, 99}, 52⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_014 : (⟨{4, 7, 19, 36, 37, 50, 60, 99}, 56⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 36, 37, 50, 60, 99}, 56⟩ : Position).afterPick 4 = (⟨{7, 19, 36, 37, 50, 60, 99}, 52⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_013]
  rfl

private theorem node_015 : (⟨{7, 19, 36, 37, 50, 57, 99}, 55⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_016 : (⟨{4, 7, 19, 36, 37, 50, 57, 99}, 59⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 36, 37, 50, 57, 99}, 59⟩ : Position).afterPick 4 = (⟨{7, 19, 36, 37, 50, 57, 99}, 55⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_015]
  rfl

private theorem node_017 : (⟨{7, 19, 36, 37, 50, 57, 60}, 94⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_018 : (⟨{4, 7, 19, 36, 37, 50, 57, 60}, 98⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60}, 98⟩ : Position).afterPick 4 = (⟨{7, 19, 36, 37, 50, 57, 60}, 94⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_017]
  rfl

private theorem node_019 : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).afterPick 4 = (⟨{7, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_002]
    rfl
  · have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).afterPick 7 = (⟨{4, 19, 36, 37, 50, 57, 60, 99}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_004]
    rfl
  · have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).afterPick 19 = (⟨{4, 7, 36, 37, 50, 57, 60, 99}, 18⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_006]
    rfl
  · have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).afterPick 36 = (⟨{4, 7, 19, 37, 50, 57, 60, 99}, 35⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_008]
    rfl
  · have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).afterPick 37 = (⟨{4, 7, 19, 36, 50, 57, 60, 99}, 36⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_010]
    rfl
  · have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).afterPick 50 = (⟨{4, 7, 19, 36, 37, 57, 60, 99}, 49⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_012]
    rfl
  · have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).afterPick 57 = (⟨{4, 7, 19, 36, 37, 50, 60, 99}, 56⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_014]
    rfl
  · have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).afterPick 60 = (⟨{4, 7, 19, 36, 37, 50, 57, 99}, 59⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_016]
    rfl
  · have he : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).afterPick 99 = (⟨{4, 7, 19, 36, 37, 50, 57, 60}, 98⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_018]
    rfl

def tailList : List ℕ := [19, 36, 37, 50, 57, 60, 99]
def tail : Finset ℕ := tailList.toFinset
def core : Finset ℕ := {4, 7} ∪ tail

/-- Pure label geometry, independent of any game value. -/
def AlternatingTail (L : List ℕ) : Prop :=
  L.Pairwise (· < ·) ∧ (∀ x ∈ L, 9 ≤ x) ∧
    (∀ i : Fin L.length, L[i] % 2 = (i.val + 1) % 2) ∧ Even L.sum

theorem tail_geometry : AlternatingTail tailList := by
  unfold AlternatingTail
  decide +kernel

theorem arithmetic_premises :
    tail.card = 7 ∧ tail.sum id = 358 ∧ Even (tail.sum id) ∧
      (∀ x ∈ tail, 9 ≤ x) ∧ core.card = 9 ∧ core.sum id = 369 := by
  decide +kernel

theorem core_one_loss : (⟨core, 1⟩ : Position).value = .loss := by
  have he : core = {4, 7, 19, 36, 37, 50, 57, 60, 99} := by decide
  simpa only [he] using node_019

theorem every_pick_loses (x : ℕ) (hx : x ∈ core) :
    (⟨core, 1⟩ : Position).moveOutcome x = .loss := by
  exact (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mp
    core_one_loss x hx

/-- A balanced allocation exists despite the proved strategic loss. -/
theorem balanced_allocation :
    ({36, 50, 99} : Finset ℕ) ⊆ core ∧
      2 * ({36, 50, 99} : Finset ℕ).sum id = core.sum id + 1 := by
  decide +kernel

/-- Alternating label parity and even tail mass do not imply nonloss. -/
theorem not_uniform_alternating_tail_nonloss :
    ¬ (∀ L : List ℕ, AlternatingTail L →
      (⟨{4, 7} ∪ L.toFinset, 1⟩ : Position).value ≠ .loss) := by
  intro h
  exact h tailList tail_geometry core_one_loss

/-- The witness can be obtained by deleting six even-length label gaps.
This is only a finite-set identity, not a legal-play assertion. -/
theorem six_gap_geometry :
    Icc 9 99 \ tail = Icc 9 18 ∪ Icc 20 35 ∪ Icc 38 49 ∪
      Icc 51 56 ∪ Icc 58 59 ∪ Icc 61 98 ∧
    ((Icc 9 99) \ tail).card = 84 ∧ Even (99 * (99 + 1) / 2) := by
  decide +kernel

/-- All omitted labels split into forty-two disjoint adjacent pairs.
No claim of reachability by those deletions is made. -/
theorem adjacent_pair_deletion_geometry :
    ∃ B : Finset ℕ, B.card = 42 ∧ Even B.card ∧
      Icc 9 99 \ tail = B ∪ B.image (fun b ↦ b + 1) ∧
      Disjoint B (B.image (fun b ↦ b + 1)) ∧
      (∀ b ∈ B, ∀ c ∈ B, b ≠ c →
        Disjoint ({b, b+1} : Finset ℕ) {c, c+1}) := by
  exact ⟨{9, 11, 13, 15, 17, 20, 22, 24, 26, 28, 30, 32, 34, 38, 40, 42, 44, 46, 48, 51, 53, 55, 58, 61, 63, 65, 67, 69, 71, 73, 75, 77, 79, 81, 83, 85, 87, 89, 91, 93, 95, 97}, by decide +kernel⟩

end CatchUp.AlternatingTailObstruction
