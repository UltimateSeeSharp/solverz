/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/UnitGuardObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.NearDeficitGuardObstruction

/-!
# A minimum counter of two does not ensure safety at deficit one

The twelve-counter sparse support has minimum two and odd counter sum,
yet loses at unit deficit. Every legal first pick is certified losing.
The proof DAG retains every losing-node choice and correct same-player continuations.
This is an obstruction to proposed induction lemmas, not to the interval conjecture.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.UnitGuardObstruction

open CatchUp (Position.value_eq_loss_iff_of_nonterminal)
open CatchUp.DeficitTwo (win_of_move)

private theorem node_001 : (⟨{19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_002 : (⟨{13, 35, 36, 50, 57, 60, 99}, 16⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_003 : (⟨{13, 19, 36, 50, 57, 60, 99}, 32⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_004 : (⟨{13, 19, 35, 50, 57, 60, 99}, 33⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_005 : (⟨{13, 19, 35, 36, 57, 60, 99}, 47⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_006 : (⟨{13, 19, 35, 36, 50, 60, 99}, 54⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_007 : (⟨{13, 19, 35, 36, 50, 57, 99}, 57⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_008 : (⟨{13, 19, 35, 36, 50, 57, 60}, 96⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_009 : (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 13 = (⟨{19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_001]
    rfl
  · have he : (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 19 = (⟨{13, 35, 36, 50, 57, 60, 99}, 16⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_002]
    rfl
  · have he : (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 35 = (⟨{13, 19, 36, 50, 57, 60, 99}, 32⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_003]
    rfl
  · have he : (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 36 = (⟨{13, 19, 35, 50, 57, 60, 99}, 33⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_004]
    rfl
  · have he : (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 50 = (⟨{13, 19, 35, 36, 57, 60, 99}, 47⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_005]
    rfl
  · have he : (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 57 = (⟨{13, 19, 35, 36, 50, 60, 99}, 54⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_006]
    rfl
  · have he : (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 60 = (⟨{13, 19, 35, 36, 50, 57, 99}, 57⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_007]
    rfl
  · have he : (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 99 = (⟨{13, 19, 35, 36, 50, 57, 60}, 96⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_008]
    rfl

private theorem node_010 : (⟨{19, 35, 36, 50, 57, 60, 99}, 4⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_011 : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 7 = (⟨{19, 35, 36, 50, 57, 60, 99}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_010]
  rfl

private theorem node_012 : (⟨{13, 35, 36, 50, 57, 60, 99}, 2⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_013 : (⟨{7, 13, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 7 = (⟨{13, 35, 36, 50, 57, 60, 99}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_012]
  rfl

private theorem node_014 : (⟨{7, 13, 19, 50, 57, 60, 99}, 11⟩ : Position).value = .loss := by
  exact CatchUp.NearDeficitGuardObstruction.node_014

private theorem node_015 : (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 25⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 25⟩ : Position).afterPick 36 = (⟨{7, 13, 19, 50, 57, 60, 99}, 11⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_014]
  rfl

private theorem node_016 : (⟨{7, 13, 19, 50, 57, 60, 99}, 9⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_017 : (⟨{7, 13, 19, 35, 50, 57, 60, 99}, 26⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 50, 57, 60, 99}, 26⟩ : Position).afterPick 35 = (⟨{7, 13, 19, 50, 57, 60, 99}, 9⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_016]
  rfl

private theorem node_018 : (⟨{13, 19, 35, 36, 57, 60, 99}, 33⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_019 : (⟨{7, 13, 19, 35, 36, 57, 60, 99}, 40⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 36, 57, 60, 99}, 40⟩ : Position).afterPick 7 = (⟨{13, 19, 35, 36, 57, 60, 99}, 33⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_018]
  rfl

private theorem node_020 : (⟨{13, 19, 35, 36, 50, 60, 99}, 40⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_021 : (⟨{7, 13, 19, 35, 36, 50, 60, 99}, 47⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 36, 50, 60, 99}, 47⟩ : Position).afterPick 7 = (⟨{13, 19, 35, 36, 50, 60, 99}, 40⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_020]
  rfl

private theorem node_022 : (⟨{13, 19, 35, 36, 50, 57, 99}, 43⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_023 : (⟨{7, 13, 19, 35, 36, 50, 57, 99}, 50⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 36, 50, 57, 99}, 50⟩ : Position).afterPick 7 = (⟨{13, 19, 35, 36, 50, 57, 99}, 43⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_022]
  rfl

private theorem node_024 : (⟨{13, 19, 35, 36, 50, 57, 60}, 82⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_025 : (⟨{7, 13, 19, 35, 36, 50, 57, 60}, 89⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60}, 89⟩ : Position).afterPick 7 = (⟨{13, 19, 35, 36, 50, 57, 60}, 82⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_024]
  rfl

private theorem node_026 : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 7 = (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_009]
    rfl
  · have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 13 = (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_011]
    rfl
  · have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 19 = (⟨{7, 13, 35, 36, 50, 57, 60, 99}, 9⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_013]
    rfl
  · have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 35 = (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 25⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_015]
    rfl
  · have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 36 = (⟨{7, 13, 19, 35, 50, 57, 60, 99}, 26⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_017]
    rfl
  · have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 50 = (⟨{7, 13, 19, 35, 36, 57, 60, 99}, 40⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_019]
    rfl
  · have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 57 = (⟨{7, 13, 19, 35, 36, 50, 60, 99}, 47⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_021]
    rfl
  · have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 60 = (⟨{7, 13, 19, 35, 36, 50, 57, 99}, 50⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_023]
    rfl
  · have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 99 = (⟨{7, 13, 19, 35, 36, 50, 57, 60}, 89⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_025]
    rfl

private theorem node_027 : (⟨{4, 19, 36, 50, 57, 60, 99}, 29⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_028 : (⟨{4, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{4, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position).afterPick 35 = (⟨{4, 19, 36, 50, 57, 60, 99}, 29⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_027]
  rfl

private theorem node_029 : (⟨{13, 35, 36, 50, 57, 60, 99}, 8⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_030 : (⟨{4, 13, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 4 = (⟨{13, 35, 36, 50, 57, 60, 99}, 8⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_029]
  rfl

private theorem node_031 : (⟨{13, 19, 36, 50, 57, 60, 99}, 24⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_032 : (⟨{4, 13, 19, 36, 50, 57, 60, 99}, 28⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 36, 50, 57, 60, 99}, 28⟩ : Position).afterPick 4 = (⟨{13, 19, 36, 50, 57, 60, 99}, 24⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_031]
  rfl

private theorem node_033 : (⟨{13, 19, 35, 50, 57, 60, 99}, 25⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_034 : (⟨{4, 13, 19, 35, 50, 57, 60, 99}, 29⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 35, 50, 57, 60, 99}, 29⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 50, 57, 60, 99}, 25⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_033]
  rfl

private theorem node_035 : (⟨{13, 19, 35, 36, 57, 60, 99}, 39⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_036 : (⟨{4, 13, 19, 35, 36, 57, 60, 99}, 43⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 35, 36, 57, 60, 99}, 43⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 36, 57, 60, 99}, 39⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_035]
  rfl

private theorem node_037 : (⟨{13, 19, 35, 36, 50, 60, 99}, 46⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_038 : (⟨{4, 13, 19, 35, 36, 50, 60, 99}, 50⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 35, 36, 50, 60, 99}, 50⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 36, 50, 60, 99}, 46⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_037]
  rfl

private theorem node_039 : (⟨{13, 19, 35, 36, 50, 57, 99}, 49⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_040 : (⟨{4, 13, 19, 35, 36, 50, 57, 99}, 53⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 35, 36, 50, 57, 99}, 53⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 36, 50, 57, 99}, 49⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_039]
  rfl

private theorem node_041 : (⟨{13, 19, 35, 36, 50, 57, 60}, 88⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_042 : (⟨{4, 13, 19, 35, 36, 50, 57, 60}, 92⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60}, 92⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 36, 50, 57, 60}, 88⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_041]
  rfl

private theorem node_043 : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_009]
    rfl
  · have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 13 = (⟨{4, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_028]
    rfl
  · have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 19 = (⟨{4, 13, 35, 36, 50, 57, 60, 99}, 12⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_030]
    rfl
  · have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 35 = (⟨{4, 13, 19, 36, 50, 57, 60, 99}, 28⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_032]
    rfl
  · have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 36 = (⟨{4, 13, 19, 35, 50, 57, 60, 99}, 29⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_034]
    rfl
  · have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 50 = (⟨{4, 13, 19, 35, 36, 57, 60, 99}, 43⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_036]
    rfl
  · have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 57 = (⟨{4, 13, 19, 35, 36, 50, 60, 99}, 50⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_038]
    rfl
  · have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 60 = (⟨{4, 13, 19, 35, 36, 50, 57, 99}, 53⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_040]
    rfl
  · have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 99 = (⟨{4, 13, 19, 35, 36, 50, 57, 60}, 92⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_042]
    rfl

private theorem node_044 : (⟨{7, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_045 : (⟨{4, 7, 35, 36, 50, 57, 60, 99}, 18⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 35, 36, 50, 57, 60, 99}, 18⟩ : Position).afterPick 4 = (⟨{7, 35, 36, 50, 57, 60, 99}, 14⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_044]
  rfl

private theorem node_046 : (⟨{4, 7, 19, 36, 57, 60, 99}, 16⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_047 : (⟨{4, 7, 19, 36, 50, 57, 60, 99}, 34⟩ : Position).value = .win := by
  apply win_of_move _ _ 50 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 36, 50, 57, 60, 99}, 34⟩ : Position).afterPick 50 = (⟨{4, 7, 19, 36, 57, 60, 99}, 16⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_046]
  rfl

private theorem node_048 : (⟨{4, 7, 19, 35, 57, 60, 99}, 15⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_049 : (⟨{4, 7, 19, 35, 50, 57, 60, 99}, 35⟩ : Position).value = .win := by
  apply win_of_move _ _ 50 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 35, 50, 57, 60, 99}, 35⟩ : Position).afterPick 50 = (⟨{4, 7, 19, 35, 57, 60, 99}, 15⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_048]
  rfl

private theorem node_050 : (⟨{7, 19, 35, 36, 57, 60, 99}, 45⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_051 : (⟨{4, 7, 19, 35, 36, 57, 60, 99}, 49⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 35, 36, 57, 60, 99}, 49⟩ : Position).afterPick 4 = (⟨{7, 19, 35, 36, 57, 60, 99}, 45⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_050]
  rfl

private theorem node_052 : (⟨{7, 19, 35, 36, 50, 60, 99}, 52⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_053 : (⟨{4, 7, 19, 35, 36, 50, 60, 99}, 56⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 35, 36, 50, 60, 99}, 56⟩ : Position).afterPick 4 = (⟨{7, 19, 35, 36, 50, 60, 99}, 52⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_052]
  rfl

private theorem node_054 : (⟨{7, 19, 35, 36, 50, 57, 99}, 55⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_055 : (⟨{4, 7, 19, 35, 36, 50, 57, 99}, 59⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 35, 36, 50, 57, 99}, 59⟩ : Position).afterPick 4 = (⟨{7, 19, 35, 36, 50, 57, 99}, 55⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_054]
  rfl

private theorem node_056 : (⟨{7, 19, 35, 36, 50, 57, 60}, 94⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_057 : (⟨{4, 7, 19, 35, 36, 50, 57, 60}, 98⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60}, 98⟩ : Position).afterPick 4 = (⟨{7, 19, 35, 36, 50, 57, 60}, 94⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_056]
  rfl

private theorem node_058 : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 4 = (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_011]
    rfl
  · have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 7 = (⟨{4, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_028]
    rfl
  · have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 19 = (⟨{4, 7, 35, 36, 50, 57, 60, 99}, 18⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_045]
    rfl
  · have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 35 = (⟨{4, 7, 19, 36, 50, 57, 60, 99}, 34⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_047]
    rfl
  · have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 36 = (⟨{4, 7, 19, 35, 50, 57, 60, 99}, 35⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_049]
    rfl
  · have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 50 = (⟨{4, 7, 19, 35, 36, 57, 60, 99}, 49⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_051]
    rfl
  · have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 57 = (⟨{4, 7, 19, 35, 36, 50, 60, 99}, 56⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_053]
    rfl
  · have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 60 = (⟨{4, 7, 19, 35, 36, 50, 57, 99}, 59⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_055]
    rfl
  · have he : (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 99 = (⟨{4, 7, 19, 35, 36, 50, 57, 60}, 98⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_057]
    rfl

private theorem node_059 : (⟨{7, 13, 36, 50, 57, 60, 99}, 26⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_060 : (⟨{4, 13, 36, 50, 57, 60, 99}, 23⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_061 : (⟨{4, 7, 36, 50, 57, 60, 99}, 17⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_062 : (⟨{4, 7, 13, 50, 57, 60, 99}, 6⟩ : Position).value = .win := by
  exact CatchUp.NearDeficitGuardObstruction.node_047

private theorem node_063 : (⟨{4, 7, 13, 36, 57, 60, 99}, 20⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_064 : (⟨{4, 7, 13, 36, 50, 60, 99}, 27⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_065 : (⟨{4, 7, 13, 36, 50, 57, 99}, 30⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_066 : (⟨{4, 7, 13, 36, 50, 57, 60}, 69⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_067 : (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 4 = (⟨{7, 13, 36, 50, 57, 60, 99}, 26⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_059]
    rfl
  · have he : (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 7 = (⟨{4, 13, 36, 50, 57, 60, 99}, 23⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_060]
    rfl
  · have he : (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 13 = (⟨{4, 7, 36, 50, 57, 60, 99}, 17⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_061]
    rfl
  · have he : (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 36 = (⟨{4, 7, 13, 50, 57, 60, 99}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_062]
    rfl
  · have he : (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 50 = (⟨{4, 7, 13, 36, 57, 60, 99}, 20⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_063]
    rfl
  · have he : (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 57 = (⟨{4, 7, 13, 36, 50, 60, 99}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_064]
    rfl
  · have he : (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 60 = (⟨{4, 7, 13, 36, 50, 57, 99}, 30⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_065]
    rfl
  · have he : (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 99 = (⟨{4, 7, 13, 36, 50, 57, 60}, 69⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_066]
    rfl

private theorem node_068 : (⟨{4, 7, 13, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 35 = (⟨{4, 7, 13, 36, 50, 57, 60, 99}, 30⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_067]
  rfl

private theorem node_069 : (⟨{7, 19, 36, 50, 57, 60, 99}, 4⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_070 : (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 17⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 17⟩ : Position).afterPick 13 = (⟨{7, 19, 36, 50, 57, 60, 99}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_069]
  rfl

private theorem node_071 : (⟨{4, 7, 13, 19, 36, 50, 57, 60, 99}, 21⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 36, 50, 57, 60, 99}, 21⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 17⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_070]
  rfl

private theorem node_072 : (⟨{7, 19, 35, 50, 57, 60, 99}, 5⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_073 : (⟨{7, 13, 19, 35, 50, 57, 60, 99}, 18⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 50, 57, 60, 99}, 18⟩ : Position).afterPick 13 = (⟨{7, 19, 35, 50, 57, 60, 99}, 5⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_072]
  rfl

private theorem node_074 : (⟨{4, 7, 13, 19, 35, 50, 57, 60, 99}, 22⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 35, 50, 57, 60, 99}, 22⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 35, 50, 57, 60, 99}, 18⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_073]
  rfl

private theorem node_075 : (⟨{7, 19, 35, 36, 57, 60, 99}, 19⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_076 : (⟨{7, 13, 19, 35, 36, 57, 60, 99}, 32⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 36, 57, 60, 99}, 32⟩ : Position).afterPick 13 = (⟨{7, 19, 35, 36, 57, 60, 99}, 19⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_075]
  rfl

private theorem node_077 : (⟨{4, 7, 13, 19, 35, 36, 57, 60, 99}, 36⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 35, 36, 57, 60, 99}, 36⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 35, 36, 57, 60, 99}, 32⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_076]
  rfl

private theorem node_078 : (⟨{7, 13, 19, 36, 50, 60, 99}, 4⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_079 : (⟨{7, 13, 19, 35, 36, 50, 60, 99}, 39⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 36, 50, 60, 99}, 39⟩ : Position).afterPick 35 = (⟨{7, 13, 19, 36, 50, 60, 99}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_078]
  rfl

private theorem node_080 : (⟨{4, 7, 13, 19, 35, 36, 50, 60, 99}, 43⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 35, 36, 50, 60, 99}, 43⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 35, 36, 50, 60, 99}, 39⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_079]
  rfl

private theorem node_081 : (⟨{13, 19, 35, 36, 50, 57, 99}, 35⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_082 : (⟨{7, 13, 19, 35, 36, 50, 57, 99}, 42⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 36, 50, 57, 99}, 42⟩ : Position).afterPick 7 = (⟨{13, 19, 35, 36, 50, 57, 99}, 35⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_081]
  rfl

private theorem node_083 : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 99}, 46⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 99}, 46⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 35, 36, 50, 57, 99}, 42⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_082]
  rfl

private theorem node_084 : (⟨{13, 19, 35, 36, 50, 57, 60}, 74⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_085 : (⟨{7, 13, 19, 35, 36, 50, 57, 60}, 81⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 35, 36, 50, 57, 60}, 81⟩ : Position).afterPick 7 = (⟨{13, 19, 35, 36, 50, 57, 60}, 74⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_084]
  rfl

private theorem node_086 : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60}, 85⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60}, 85⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 35, 36, 50, 57, 60}, 81⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_085]
  rfl

private theorem node_087 : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_026]
    rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 7 = (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_043]
    rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 13 = (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_058]
    rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 19 = (⟨{4, 7, 13, 35, 36, 50, 57, 60, 99}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_068]
    rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 35 = (⟨{4, 7, 13, 19, 36, 50, 57, 60, 99}, 21⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_071]
    rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 36 = (⟨{4, 7, 13, 19, 35, 50, 57, 60, 99}, 22⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_074]
    rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 50 = (⟨{4, 7, 13, 19, 35, 36, 57, 60, 99}, 36⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_077]
    rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 57 = (⟨{4, 7, 13, 19, 35, 36, 50, 60, 99}, 43⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_080]
    rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 60 = (⟨{4, 7, 13, 19, 35, 36, 50, 57, 99}, 46⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_083]
    rfl
  · have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 99 = (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60}, 85⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_086]
    rfl

private theorem node_088 : (⟨{4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).value = .win := by
  apply win_of_move _ _ 15 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 15 = (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_087]
  rfl

private theorem node_089 : (⟨{15, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_090 : (⟨{15, 19, 36, 50, 57, 60, 99}, 30⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_091 : (⟨{15, 19, 35, 50, 57, 60, 99}, 31⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_092 : (⟨{15, 19, 35, 36, 57, 60, 99}, 45⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_093 : (⟨{15, 19, 35, 36, 50, 60, 99}, 52⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_094 : (⟨{15, 19, 35, 36, 50, 57, 99}, 55⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_095 : (⟨{15, 19, 35, 36, 50, 57, 60}, 94⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_096 : (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 15 = (⟨{19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_001]
    rfl
  · have he : (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 19 = (⟨{15, 35, 36, 50, 57, 60, 99}, 14⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_089]
    rfl
  · have he : (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 35 = (⟨{15, 19, 36, 50, 57, 60, 99}, 30⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_090]
    rfl
  · have he : (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 36 = (⟨{15, 19, 35, 50, 57, 60, 99}, 31⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_091]
    rfl
  · have he : (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 50 = (⟨{15, 19, 35, 36, 57, 60, 99}, 45⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_092]
    rfl
  · have he : (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 57 = (⟨{15, 19, 35, 36, 50, 60, 99}, 52⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_093]
    rfl
  · have he : (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 60 = (⟨{15, 19, 35, 36, 50, 57, 99}, 55⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_094]
    rfl
  · have he : (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 99 = (⟨{15, 19, 35, 36, 50, 57, 60}, 94⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_095]
    rfl

private theorem node_097 : (⟨{7, 15, 36, 50, 57, 60, 99}, 28⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_098 : (⟨{7, 15, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{7, 15, 35, 36, 50, 57, 60, 99}, 7⟩ : Position).afterPick 35 = (⟨{7, 15, 36, 50, 57, 60, 99}, 28⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_097]
  rfl

private theorem node_099 : (⟨{15, 19, 36, 50, 57, 60, 99}, 16⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_100 : (⟨{7, 15, 19, 36, 50, 57, 60, 99}, 23⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 15, 19, 36, 50, 57, 60, 99}, 23⟩ : Position).afterPick 7 = (⟨{15, 19, 36, 50, 57, 60, 99}, 16⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_099]
  rfl

private theorem node_101 : (⟨{7, 15, 19, 50, 57, 60, 99}, 11⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_102 : (⟨{7, 15, 19, 35, 50, 57, 60, 99}, 24⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{7, 15, 19, 35, 50, 57, 60, 99}, 24⟩ : Position).afterPick 35 = (⟨{7, 15, 19, 50, 57, 60, 99}, 11⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_101]
  rfl

private theorem node_103 : (⟨{7, 19, 35, 36, 57, 60, 99}, 23⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_104 : (⟨{7, 15, 19, 35, 36, 57, 60, 99}, 38⟩ : Position).value = .win := by
  apply win_of_move _ _ 15 (by decide) (by decide)
  have he : (⟨{7, 15, 19, 35, 36, 57, 60, 99}, 38⟩ : Position).afterPick 15 = (⟨{7, 19, 35, 36, 57, 60, 99}, 23⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_103]
  rfl

private theorem node_105 : (⟨{15, 19, 35, 36, 50, 60, 99}, 38⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_106 : (⟨{7, 15, 19, 35, 36, 50, 60, 99}, 45⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 15, 19, 35, 36, 50, 60, 99}, 45⟩ : Position).afterPick 7 = (⟨{15, 19, 35, 36, 50, 60, 99}, 38⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_105]
  rfl

private theorem node_107 : (⟨{15, 19, 35, 36, 50, 57, 99}, 41⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_108 : (⟨{7, 15, 19, 35, 36, 50, 57, 99}, 48⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 15, 19, 35, 36, 50, 57, 99}, 48⟩ : Position).afterPick 7 = (⟨{15, 19, 35, 36, 50, 57, 99}, 41⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_107]
  rfl

private theorem node_109 : (⟨{15, 19, 35, 36, 50, 57, 60}, 80⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_110 : (⟨{7, 15, 19, 35, 36, 50, 57, 60}, 87⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60}, 87⟩ : Position).afterPick 7 = (⟨{15, 19, 35, 36, 50, 57, 60}, 80⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_109]
  rfl

private theorem node_111 : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 7 = (⟨{15, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_096]
    rfl
  · have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 15 = (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_011]
    rfl
  · have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 19 = (⟨{7, 15, 35, 36, 50, 57, 60, 99}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_098]
    rfl
  · have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 35 = (⟨{7, 15, 19, 36, 50, 57, 60, 99}, 23⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_100]
    rfl
  · have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 36 = (⟨{7, 15, 19, 35, 50, 57, 60, 99}, 24⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_102]
    rfl
  · have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 50 = (⟨{7, 15, 19, 35, 36, 57, 60, 99}, 38⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_104]
    rfl
  · have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 57 = (⟨{7, 15, 19, 35, 36, 50, 60, 99}, 45⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_106]
    rfl
  · have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 60 = (⟨{7, 15, 19, 35, 36, 50, 57, 99}, 48⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_108]
    rfl
  · have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 99 = (⟨{7, 15, 19, 35, 36, 50, 57, 60}, 87⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_110]
    rfl

private theorem node_112 : (⟨{7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 13 = (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_111]
  rfl

private theorem node_113 : (⟨{2, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position).afterPick 2 = (⟨{7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_112]
  rfl

private theorem node_114 : (⟨{2, 19, 36, 50, 57, 60, 99}, 27⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_115 : (⟨{2, 19, 35, 36, 50, 57, 60, 99}, 8⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{2, 19, 35, 36, 50, 57, 60, 99}, 8⟩ : Position).afterPick 35 = (⟨{2, 19, 36, 50, 57, 60, 99}, 27⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_114]
  rfl

private theorem node_116 : (⟨{2, 13, 36, 50, 57, 60, 99}, 21⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_117 : (⟨{2, 13, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{2, 13, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 35 = (⟨{2, 13, 36, 50, 57, 60, 99}, 21⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_116]
  rfl

private theorem node_118 : (⟨{13, 19, 36, 50, 57, 60, 99}, 28⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_119 : (⟨{2, 13, 19, 36, 50, 57, 60, 99}, 30⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 13, 19, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 2 = (⟨{13, 19, 36, 50, 57, 60, 99}, 28⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_118]
  rfl

private theorem node_120 : (⟨{13, 19, 35, 50, 57, 60, 99}, 29⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_121 : (⟨{2, 13, 19, 35, 50, 57, 60, 99}, 31⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 13, 19, 35, 50, 57, 60, 99}, 31⟩ : Position).afterPick 2 = (⟨{13, 19, 35, 50, 57, 60, 99}, 29⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_120]
  rfl

private theorem node_122 : (⟨{13, 19, 35, 36, 57, 60, 99}, 43⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_123 : (⟨{2, 13, 19, 35, 36, 57, 60, 99}, 45⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 13, 19, 35, 36, 57, 60, 99}, 45⟩ : Position).afterPick 2 = (⟨{13, 19, 35, 36, 57, 60, 99}, 43⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_122]
  rfl

private theorem node_124 : (⟨{13, 19, 35, 36, 50, 60, 99}, 50⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_125 : (⟨{2, 13, 19, 35, 36, 50, 60, 99}, 52⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 13, 19, 35, 36, 50, 60, 99}, 52⟩ : Position).afterPick 2 = (⟨{13, 19, 35, 36, 50, 60, 99}, 50⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_124]
  rfl

private theorem node_126 : (⟨{13, 19, 35, 36, 50, 57, 99}, 53⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_127 : (⟨{2, 13, 19, 35, 36, 50, 57, 99}, 55⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 13, 19, 35, 36, 50, 57, 99}, 55⟩ : Position).afterPick 2 = (⟨{13, 19, 35, 36, 50, 57, 99}, 53⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_126]
  rfl

private theorem node_128 : (⟨{13, 19, 35, 36, 50, 57, 60}, 92⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_129 : (⟨{2, 13, 19, 35, 36, 50, 57, 60}, 94⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60}, 94⟩ : Position).afterPick 2 = (⟨{13, 19, 35, 36, 50, 57, 60}, 92⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_128]
  rfl

private theorem node_130 : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 2 = (⟨{13, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_009]
    rfl
  · have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 13 = (⟨{2, 19, 35, 36, 50, 57, 60, 99}, 8⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_115]
    rfl
  · have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 19 = (⟨{2, 13, 35, 36, 50, 57, 60, 99}, 14⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_117]
    rfl
  · have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 35 = (⟨{2, 13, 19, 36, 50, 57, 60, 99}, 30⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_119]
    rfl
  · have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 36 = (⟨{2, 13, 19, 35, 50, 57, 60, 99}, 31⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_121]
    rfl
  · have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 50 = (⟨{2, 13, 19, 35, 36, 57, 60, 99}, 45⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_123]
    rfl
  · have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 57 = (⟨{2, 13, 19, 35, 36, 50, 60, 99}, 52⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_125]
    rfl
  · have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 60 = (⟨{2, 13, 19, 35, 36, 50, 57, 99}, 55⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_127]
    rfl
  · have he : (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position).afterPick 99 = (⟨{2, 13, 19, 35, 36, 50, 57, 60}, 94⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_129]
    rfl

private theorem node_131 : (⟨{19, 35, 36, 50, 57, 60, 99}, 2⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_132 : (⟨{4, 19, 35, 36, 50, 57, 60, 99}, 2⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 19, 35, 36, 50, 57, 60, 99}, 2⟩ : Position).afterPick 4 = (⟨{19, 35, 36, 50, 57, 60, 99}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_131]
  rfl

private theorem node_133 : (⟨{2, 4, 19, 35, 36, 50, 57, 60, 99}, 4⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 19, 35, 36, 50, 57, 60, 99}, 4⟩ : Position).afterPick 2 = (⟨{4, 19, 35, 36, 50, 57, 60, 99}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_132]
  rfl

private theorem node_134 : (⟨{13, 35, 36, 50, 57, 60, 99}, 4⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_135 : (⟨{4, 13, 35, 36, 50, 57, 60, 99}, 8⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 35, 36, 50, 57, 60, 99}, 8⟩ : Position).afterPick 4 = (⟨{13, 35, 36, 50, 57, 60, 99}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_134]
  rfl

private theorem node_136 : (⟨{2, 4, 13, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 13, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 2 = (⟨{4, 13, 35, 36, 50, 57, 60, 99}, 8⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_135]
  rfl

private theorem node_137 : (⟨{13, 19, 36, 50, 57, 60, 99}, 20⟩ : Position).value = .win := by
  exact CatchUp.NearDeficitGuardObstruction.node_016

private theorem node_138 : (⟨{4, 13, 19, 36, 50, 57, 60, 99}, 24⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 36, 50, 57, 60, 99}, 24⟩ : Position).afterPick 4 = (⟨{13, 19, 36, 50, 57, 60, 99}, 20⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_137]
  rfl

private theorem node_139 : (⟨{2, 4, 13, 19, 36, 50, 57, 60, 99}, 26⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 13, 19, 36, 50, 57, 60, 99}, 26⟩ : Position).afterPick 2 = (⟨{4, 13, 19, 36, 50, 57, 60, 99}, 24⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_138]
  rfl

private theorem node_140 : (⟨{4, 13, 19, 50, 57, 60, 99}, 6⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_141 : (⟨{2, 13, 19, 50, 57, 60, 99}, 4⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_142 : (⟨{2, 4, 19, 50, 57, 60, 99}, 5⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_143 : (⟨{2, 4, 13, 50, 57, 60, 99}, 11⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_144 : (⟨{2, 4, 13, 19, 57, 60, 99}, 42⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_145 : (⟨{2, 4, 13, 19, 50, 60, 99}, 49⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_146 : (⟨{2, 4, 13, 19, 50, 57, 99}, 52⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_147 : (⟨{2, 4, 13, 19, 50, 57, 60}, 91⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_148 : (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position).afterPick 2 = (⟨{4, 13, 19, 50, 57, 60, 99}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_140]
    rfl
  · have he : (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position).afterPick 4 = (⟨{2, 13, 19, 50, 57, 60, 99}, 4⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_141]
    rfl
  · have he : (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position).afterPick 13 = (⟨{2, 4, 19, 50, 57, 60, 99}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_142]
    rfl
  · have he : (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position).afterPick 19 = (⟨{2, 4, 13, 50, 57, 60, 99}, 11⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_143]
    rfl
  · have he : (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position).afterPick 50 = (⟨{2, 4, 13, 19, 57, 60, 99}, 42⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_144]
    rfl
  · have he : (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position).afterPick 57 = (⟨{2, 4, 13, 19, 50, 60, 99}, 49⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_145]
    rfl
  · have he : (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position).afterPick 60 = (⟨{2, 4, 13, 19, 50, 57, 99}, 52⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_146]
    rfl
  · have he : (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position).afterPick 99 = (⟨{2, 4, 13, 19, 50, 57, 60}, 91⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_147]
    rfl

private theorem node_149 : (⟨{2, 4, 13, 19, 35, 50, 57, 60, 99}, 27⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{2, 4, 13, 19, 35, 50, 57, 60, 99}, 27⟩ : Position).afterPick 35 = (⟨{2, 4, 13, 19, 50, 57, 60, 99}, 8⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_148]
  rfl

private theorem node_150 : (⟨{13, 19, 35, 36, 57, 60, 99}, 35⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_151 : (⟨{4, 13, 19, 35, 36, 57, 60, 99}, 39⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 35, 36, 57, 60, 99}, 39⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 36, 57, 60, 99}, 35⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_150]
  rfl

private theorem node_152 : (⟨{2, 4, 13, 19, 35, 36, 57, 60, 99}, 41⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 13, 19, 35, 36, 57, 60, 99}, 41⟩ : Position).afterPick 2 = (⟨{4, 13, 19, 35, 36, 57, 60, 99}, 39⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_151]
  rfl

private theorem node_153 : (⟨{13, 19, 35, 36, 50, 60, 99}, 42⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_154 : (⟨{4, 13, 19, 35, 36, 50, 60, 99}, 46⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 35, 36, 50, 60, 99}, 46⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 36, 50, 60, 99}, 42⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_153]
  rfl

private theorem node_155 : (⟨{2, 4, 13, 19, 35, 36, 50, 60, 99}, 48⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 13, 19, 35, 36, 50, 60, 99}, 48⟩ : Position).afterPick 2 = (⟨{4, 13, 19, 35, 36, 50, 60, 99}, 46⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_154]
  rfl

private theorem node_156 : (⟨{13, 19, 35, 36, 50, 57, 99}, 45⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_157 : (⟨{4, 13, 19, 35, 36, 50, 57, 99}, 49⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 35, 36, 50, 57, 99}, 49⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 36, 50, 57, 99}, 45⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_156]
  rfl

private theorem node_158 : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 99}, 51⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 99}, 51⟩ : Position).afterPick 2 = (⟨{4, 13, 19, 35, 36, 50, 57, 99}, 49⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_157]
  rfl

private theorem node_159 : (⟨{13, 19, 35, 36, 50, 57, 60}, 84⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_160 : (⟨{4, 13, 19, 35, 36, 50, 57, 60}, 88⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 35, 36, 50, 57, 60}, 88⟩ : Position).afterPick 4 = (⟨{13, 19, 35, 36, 50, 57, 60}, 84⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_159]
  rfl

private theorem node_161 : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60}, 90⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60}, 90⟩ : Position).afterPick 2 = (⟨{4, 13, 19, 35, 36, 50, 57, 60}, 88⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_160]
  rfl

private theorem node_162 : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 2 = (⟨{4, 13, 19, 35, 36, 50, 57, 60, 99}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_043]
    rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 4 = (⟨{2, 13, 19, 35, 36, 50, 57, 60, 99}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_130]
    rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 13 = (⟨{2, 4, 19, 35, 36, 50, 57, 60, 99}, 4⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_133]
    rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 19 = (⟨{2, 4, 13, 35, 36, 50, 57, 60, 99}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_136]
    rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 35 = (⟨{2, 4, 13, 19, 36, 50, 57, 60, 99}, 26⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_139]
    rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 36 = (⟨{2, 4, 13, 19, 35, 50, 57, 60, 99}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_149]
    rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 50 = (⟨{2, 4, 13, 19, 35, 36, 57, 60, 99}, 41⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_152]
    rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 57 = (⟨{2, 4, 13, 19, 35, 36, 50, 60, 99}, 48⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_155]
    rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 60 = (⟨{2, 4, 13, 19, 35, 36, 50, 57, 99}, 51⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_158]
    rfl
  · have he : (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 99 = (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60}, 90⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_161]
    rfl

private theorem node_163 : (⟨{2, 4, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position).value = .win := by
  apply win_of_move _ _ 15 (by decide) (by decide)
  have he : (⟨{2, 4, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position).afterPick 15 = (⟨{2, 4, 13, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_162]
  rfl

private theorem node_164 : (⟨{7, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_165 : (⟨{7, 19, 36, 50, 57, 60, 99}, 26⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_166 : (⟨{7, 19, 35, 50, 57, 60, 99}, 27⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_167 : (⟨{7, 19, 35, 36, 57, 60, 99}, 41⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_168 : (⟨{7, 19, 35, 36, 50, 60, 99}, 48⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_169 : (⟨{7, 19, 35, 36, 50, 57, 99}, 51⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_170 : (⟨{7, 19, 35, 36, 50, 57, 60}, 90⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_171 : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 7 = (⟨{19, 35, 36, 50, 57, 60, 99}, 2⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_131]
    rfl
  · have he : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 19 = (⟨{7, 35, 36, 50, 57, 60, 99}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_164]
    rfl
  · have he : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 35 = (⟨{7, 19, 36, 50, 57, 60, 99}, 26⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_165]
    rfl
  · have he : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 36 = (⟨{7, 19, 35, 50, 57, 60, 99}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_166]
    rfl
  · have he : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 50 = (⟨{7, 19, 35, 36, 57, 60, 99}, 41⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_167]
    rfl
  · have he : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 57 = (⟨{7, 19, 35, 36, 50, 60, 99}, 48⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_168]
    rfl
  · have he : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 60 = (⟨{7, 19, 35, 36, 50, 57, 99}, 51⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_169]
    rfl
  · have he : (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position).afterPick 99 = (⟨{7, 19, 35, 36, 50, 57, 60}, 90⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_170]
    rfl

private theorem node_172 : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position).value = .win := by
  apply win_of_move _ _ 15 (by decide) (by decide)
  have he : (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position).afterPick 15 = (⟨{7, 19, 35, 36, 50, 57, 60, 99}, 9⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_171]
  rfl

private theorem node_173 : (⟨{4, 7, 15, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 15, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position).afterPick 4 = (⟨{7, 15, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_172]
  rfl

private theorem node_174 : (⟨{2, 4, 7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 2 = (⟨{4, 7, 15, 19, 35, 36, 50, 57, 60, 99}, 10⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_173]
  rfl

private theorem node_175 : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 13 = (⟨{4, 7, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_058]
  rfl

private theorem node_176 : (⟨{2, 4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position).afterPick 2 = (⟨{4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_175]
  rfl

private theorem node_177 : (⟨{13, 15, 35, 36, 50, 57, 99}, 41⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_178 : (⟨{7, 15, 35, 36, 50, 57, 99}, 35⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_179 : (⟨{7, 13, 35, 36, 50, 57, 99}, 33⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_180 : (⟨{7, 13, 15, 36, 50, 57, 99}, 13⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_181 : (⟨{7, 13, 15, 35, 50, 57, 99}, 12⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_182 : (⟨{7, 13, 15, 35, 36, 57, 99}, 2⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_183 : (⟨{7, 13, 15, 35, 36, 50, 99}, 9⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_184 : (⟨{7, 13, 15, 35, 36, 50, 57}, 51⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_185 : (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position).afterPick 7 = (⟨{13, 15, 35, 36, 50, 57, 99}, 41⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_177]
    rfl
  · have he : (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position).afterPick 13 = (⟨{7, 15, 35, 36, 50, 57, 99}, 35⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_178]
    rfl
  · have he : (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position).afterPick 15 = (⟨{7, 13, 35, 36, 50, 57, 99}, 33⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_179]
    rfl
  · have he : (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position).afterPick 35 = (⟨{7, 13, 15, 36, 50, 57, 99}, 13⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_180]
    rfl
  · have he : (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position).afterPick 36 = (⟨{7, 13, 15, 35, 50, 57, 99}, 12⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_181]
    rfl
  · have he : (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position).afterPick 50 = (⟨{7, 13, 15, 35, 36, 57, 99}, 2⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_182]
    rfl
  · have he : (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position).afterPick 57 = (⟨{7, 13, 15, 35, 36, 50, 99}, 9⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_183]
    rfl
  · have he : (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position).afterPick 99 = (⟨{7, 13, 15, 35, 36, 50, 57}, 51⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_184]
    rfl

private theorem node_186 : (⟨{7, 13, 15, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).value = .win := by
  apply win_of_move _ _ 60 (by decide) (by decide)
  have he : (⟨{7, 13, 15, 35, 36, 50, 57, 60, 99}, 12⟩ : Position).afterPick 60 = (⟨{7, 13, 15, 35, 36, 50, 57, 99}, 48⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_185]
  rfl

private theorem node_187 : (⟨{4, 7, 13, 15, 35, 36, 50, 57, 60, 99}, 16⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 15, 35, 36, 50, 57, 60, 99}, 16⟩ : Position).afterPick 4 = (⟨{7, 13, 15, 35, 36, 50, 57, 60, 99}, 12⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_186]
  rfl

private theorem node_188 : (⟨{2, 4, 7, 13, 15, 35, 36, 50, 57, 60, 99}, 18⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 13, 15, 35, 36, 50, 57, 60, 99}, 18⟩ : Position).afterPick 2 = (⟨{4, 7, 13, 15, 35, 36, 50, 57, 60, 99}, 16⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_187]
  rfl

private theorem node_189 : (⟨{15, 19, 36, 50, 57, 60, 99}, 8⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_190 : (⟨{13, 15, 19, 36, 50, 57, 60, 99}, 21⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{13, 15, 19, 36, 50, 57, 60, 99}, 21⟩ : Position).afterPick 13 = (⟨{15, 19, 36, 50, 57, 60, 99}, 8⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_189]
  rfl

private theorem node_191 : (⟨{7, 13, 15, 19, 36, 50, 57, 60, 99}, 28⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 15, 19, 36, 50, 57, 60, 99}, 28⟩ : Position).afterPick 7 = (⟨{13, 15, 19, 36, 50, 57, 60, 99}, 21⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_190]
  rfl

private theorem node_192 : (⟨{4, 7, 13, 15, 19, 36, 50, 57, 60, 99}, 32⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 15, 19, 36, 50, 57, 60, 99}, 32⟩ : Position).afterPick 4 = (⟨{7, 13, 15, 19, 36, 50, 57, 60, 99}, 28⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_191]
  rfl

private theorem node_193 : (⟨{2, 4, 7, 13, 15, 19, 36, 50, 57, 60, 99}, 34⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 13, 15, 19, 36, 50, 57, 60, 99}, 34⟩ : Position).afterPick 2 = (⟨{4, 7, 13, 15, 19, 36, 50, 57, 60, 99}, 32⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_192]
  rfl

private theorem node_194 : (⟨{15, 19, 35, 50, 57, 60, 99}, 9⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_195 : (⟨{13, 15, 19, 35, 50, 57, 60, 99}, 22⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{13, 15, 19, 35, 50, 57, 60, 99}, 22⟩ : Position).afterPick 13 = (⟨{15, 19, 35, 50, 57, 60, 99}, 9⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_194]
  rfl

private theorem node_196 : (⟨{7, 13, 15, 19, 35, 50, 57, 60, 99}, 29⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 15, 19, 35, 50, 57, 60, 99}, 29⟩ : Position).afterPick 7 = (⟨{13, 15, 19, 35, 50, 57, 60, 99}, 22⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_195]
  rfl

private theorem node_197 : (⟨{4, 7, 13, 15, 19, 35, 50, 57, 60, 99}, 33⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 15, 19, 35, 50, 57, 60, 99}, 33⟩ : Position).afterPick 4 = (⟨{7, 13, 15, 19, 35, 50, 57, 60, 99}, 29⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_196]
  rfl

private theorem node_198 : (⟨{2, 4, 7, 13, 15, 19, 35, 50, 57, 60, 99}, 35⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 13, 15, 19, 35, 50, 57, 60, 99}, 35⟩ : Position).afterPick 2 = (⟨{4, 7, 13, 15, 19, 35, 50, 57, 60, 99}, 33⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_197]
  rfl

private theorem node_199 : (⟨{13, 19, 35, 36, 57, 60, 99}, 21⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_200 : (⟨{13, 15, 19, 35, 36, 57, 60, 99}, 36⟩ : Position).value = .win := by
  apply win_of_move _ _ 15 (by decide) (by decide)
  have he : (⟨{13, 15, 19, 35, 36, 57, 60, 99}, 36⟩ : Position).afterPick 15 = (⟨{13, 19, 35, 36, 57, 60, 99}, 21⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_199]
  rfl

private theorem node_201 : (⟨{7, 13, 15, 19, 35, 36, 57, 60, 99}, 43⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 15, 19, 35, 36, 57, 60, 99}, 43⟩ : Position).afterPick 7 = (⟨{13, 15, 19, 35, 36, 57, 60, 99}, 36⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_200]
  rfl

private theorem node_202 : (⟨{4, 7, 13, 15, 19, 35, 36, 57, 60, 99}, 47⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 15, 19, 35, 36, 57, 60, 99}, 47⟩ : Position).afterPick 4 = (⟨{7, 13, 15, 19, 35, 36, 57, 60, 99}, 43⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_201]
  rfl

private theorem node_203 : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 57, 60, 99}, 49⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 57, 60, 99}, 49⟩ : Position).afterPick 2 = (⟨{4, 7, 13, 15, 19, 35, 36, 57, 60, 99}, 47⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_202]
  rfl

private theorem node_204 : (⟨{15, 19, 35, 36, 50, 60, 99}, 30⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_205 : (⟨{13, 15, 19, 35, 36, 50, 60, 99}, 43⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{13, 15, 19, 35, 36, 50, 60, 99}, 43⟩ : Position).afterPick 13 = (⟨{15, 19, 35, 36, 50, 60, 99}, 30⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_204]
  rfl

private theorem node_206 : (⟨{7, 13, 15, 19, 35, 36, 50, 60, 99}, 50⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 15, 19, 35, 36, 50, 60, 99}, 50⟩ : Position).afterPick 7 = (⟨{13, 15, 19, 35, 36, 50, 60, 99}, 43⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_205]
  rfl

private theorem node_207 : (⟨{4, 7, 13, 15, 19, 35, 36, 50, 60, 99}, 54⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 15, 19, 35, 36, 50, 60, 99}, 54⟩ : Position).afterPick 4 = (⟨{7, 13, 15, 19, 35, 36, 50, 60, 99}, 50⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_206]
  rfl

private theorem node_208 : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 60, 99}, 56⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 60, 99}, 56⟩ : Position).afterPick 2 = (⟨{4, 7, 13, 15, 19, 35, 36, 50, 60, 99}, 54⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_207]
  rfl

private theorem node_209 : (⟨{13, 15, 19, 36, 50, 57, 99}, 11⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_210 : (⟨{13, 15, 19, 35, 36, 50, 57, 99}, 46⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{13, 15, 19, 35, 36, 50, 57, 99}, 46⟩ : Position).afterPick 35 = (⟨{13, 15, 19, 36, 50, 57, 99}, 11⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_209]
  rfl

private theorem node_211 : (⟨{7, 13, 15, 19, 35, 36, 50, 57, 99}, 53⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 15, 19, 35, 36, 50, 57, 99}, 53⟩ : Position).afterPick 7 = (⟨{13, 15, 19, 35, 36, 50, 57, 99}, 46⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_210]
  rfl

private theorem node_212 : (⟨{4, 7, 13, 15, 19, 35, 36, 50, 57, 99}, 57⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 15, 19, 35, 36, 50, 57, 99}, 57⟩ : Position).afterPick 4 = (⟨{7, 13, 15, 19, 35, 36, 50, 57, 99}, 53⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_211]
  rfl

private theorem node_213 : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 99}, 59⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 99}, 59⟩ : Position).afterPick 2 = (⟨{4, 7, 13, 15, 19, 35, 36, 50, 57, 99}, 57⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_212]
  rfl

private theorem node_214 : (⟨{15, 19, 35, 36, 50, 57, 60}, 72⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_215 : (⟨{13, 15, 19, 35, 36, 50, 57, 60}, 85⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{13, 15, 19, 35, 36, 50, 57, 60}, 85⟩ : Position).afterPick 13 = (⟨{15, 19, 35, 36, 50, 57, 60}, 72⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_214]
  rfl

private theorem node_216 : (⟨{7, 13, 15, 19, 35, 36, 50, 57, 60}, 92⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 15, 19, 35, 36, 50, 57, 60}, 92⟩ : Position).afterPick 7 = (⟨{13, 15, 19, 35, 36, 50, 57, 60}, 85⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_215]
  rfl

private theorem node_217 : (⟨{4, 7, 13, 15, 19, 35, 36, 50, 57, 60}, 96⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 15, 19, 35, 36, 50, 57, 60}, 96⟩ : Position).afterPick 4 = (⟨{7, 13, 15, 19, 35, 36, 50, 57, 60}, 92⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_216]
  rfl

private theorem node_218 : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60}, 98⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60}, 98⟩ : Position).afterPick 2 = (⟨{4, 7, 13, 15, 19, 35, 36, 50, 57, 60}, 96⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_217]
  rfl

private theorem node_219 : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 2 = (⟨{4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_088]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 4 = (⟨{2, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_113]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 7 = (⟨{2, 4, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_163]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 13 = (⟨{2, 4, 7, 15, 19, 35, 36, 50, 57, 60, 99}, 12⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_174]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 15 = (⟨{2, 4, 7, 13, 19, 35, 36, 50, 57, 60, 99}, 14⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_176]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 19 = (⟨{2, 4, 7, 13, 15, 35, 36, 50, 57, 60, 99}, 18⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_188]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 35 = (⟨{2, 4, 7, 13, 15, 19, 36, 50, 57, 60, 99}, 34⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_193]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 36 = (⟨{2, 4, 7, 13, 15, 19, 35, 50, 57, 60, 99}, 35⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_198]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 50 = (⟨{2, 4, 7, 13, 15, 19, 35, 36, 57, 60, 99}, 49⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_203]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 57 = (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 60, 99}, 56⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_208]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 60 = (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 99}, 59⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_213]
    rfl
  · have he : (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}, 1⟩ : Position).afterPick 99 = (⟨{2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60}, 98⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_218]
    rfl

def support : Finset ℕ := {2, 4, 7, 13, 15, 19, 35, 36, 50, 57, 60, 99}

theorem guard_loss : (⟨support, 1⟩ : Position).value = .loss :=
  node_219

theorem arithmetic_premises :
    support.card = 12 ∧ support.sum id = 397 ∧ Odd (support.sum id) ∧
      Even (1 + support.sum id) ∧ 2 ∈ support ∧
      (∀ x ∈ support, 2 ≤ x) ∧ 1 ≤ support.sum id := by
  decide +kernel

theorem every_pick_loses (x : ℕ) (hx : x ∈ support) :
    (⟨support, 1⟩ : Position).moveOutcome x = .loss := by
  exact (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mp
    guard_loss x hx

theorem reference_loss : valueAux support 0 1 false = .loss := by
  exact (Position.value_eq_value_aux support 0 1 (by decide)).symm.trans guard_loss

theorem not_unit_guard_nonloss :
    ¬ (∀ R : Finset ℕ, 2 ∈ R → (∀ x ∈ R, 2 ≤ x) → Odd (R.sum id) →
      (⟨R, 1⟩ : Position).value ≠ .loss) := by
  intro h
  exact h support (by decide) (by decide) (by decide) guard_loss



end CatchUp.UnitGuardObstruction
