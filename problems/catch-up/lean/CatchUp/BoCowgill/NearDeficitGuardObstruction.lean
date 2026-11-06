/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/NearDeficitGuardObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.AlternatingTailObstruction

/-!
# A counter one below the deficit does not guarantee safety

The sparse parent loses despite even effective total and an available counter
one below its deficit. Inserting counter two turns it into a win.
The proof DAG retains every losing-node choice and correct same-player continuations.
This is an obstruction to proposed induction lemmas, not to the interval conjecture.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.NearDeficitGuardObstruction

open CatchUp (Position.value_eq_loss_iff_of_nonterminal)
open CatchUp.DeficitTwo (win_of_move)

private theorem node_001 : (⟨{19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_002 : (⟨{13, 36, 37, 50, 57, 60, 99}, 16⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_003 : (⟨{13, 19, 37, 50, 57, 60, 99}, 33⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_004 : (⟨{13, 19, 36, 50, 57, 60, 99}, 34⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_005 : (⟨{13, 19, 36, 37, 57, 60, 99}, 47⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_006 : (⟨{13, 19, 36, 37, 50, 60, 99}, 54⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_007 : (⟨{13, 19, 36, 37, 50, 57, 99}, 57⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_008 : (⟨{13, 19, 36, 37, 50, 57, 60}, 96⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_009 : (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 13 = (⟨{19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_001]
    rfl
  · have he : (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 19 = (⟨{13, 36, 37, 50, 57, 60, 99}, 16⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_002]
    rfl
  · have he : (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 36 = (⟨{13, 19, 37, 50, 57, 60, 99}, 33⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_003]
    rfl
  · have he : (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 37 = (⟨{13, 19, 36, 50, 57, 60, 99}, 34⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_004]
    rfl
  · have he : (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 50 = (⟨{13, 19, 36, 37, 57, 60, 99}, 47⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_005]
    rfl
  · have he : (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 57 = (⟨{13, 19, 36, 37, 50, 60, 99}, 54⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_006]
    rfl
  · have he : (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 60 = (⟨{13, 19, 36, 37, 50, 57, 99}, 57⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_007]
    rfl
  · have he : (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 99 = (⟨{13, 19, 36, 37, 50, 57, 60}, 96⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_008]
    rfl

private theorem node_010 : (⟨{19, 36, 37, 50, 57, 60, 99}, 4⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_011 : (⟨{7, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position).afterPick 7 = (⟨{19, 36, 37, 50, 57, 60, 99}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_010]
  rfl

private theorem node_012 : (⟨{13, 36, 37, 50, 57, 60, 99}, 2⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_013 : (⟨{7, 13, 36, 37, 50, 57, 60, 99}, 9⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 36, 37, 50, 57, 60, 99}, 9⟩ : Position).afterPick 7 = (⟨{13, 36, 37, 50, 57, 60, 99}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_012]
  rfl

theorem node_014 : (⟨{7, 13, 19, 50, 57, 60, 99}, 11⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_015 : (⟨{7, 13, 19, 37, 50, 57, 60, 99}, 26⟩ : Position).value = .win := by
  apply win_of_move _ _ 37 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 37, 50, 57, 60, 99}, 26⟩ : Position).afterPick 37 = (⟨{7, 13, 19, 50, 57, 60, 99}, 11⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_014]
  rfl

theorem node_016 : (⟨{13, 19, 36, 50, 57, 60, 99}, 20⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_017 : (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 27⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 27⟩ : Position).afterPick 7 = (⟨{13, 19, 36, 50, 57, 60, 99}, 20⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_016]
  rfl

private theorem node_018 : (⟨{13, 19, 36, 37, 57, 60, 99}, 33⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_019 : (⟨{7, 13, 19, 36, 37, 57, 60, 99}, 40⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 37, 57, 60, 99}, 40⟩ : Position).afterPick 7 = (⟨{13, 19, 36, 37, 57, 60, 99}, 33⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_018]
  rfl

private theorem node_020 : (⟨{13, 19, 36, 37, 50, 60, 99}, 40⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_021 : (⟨{7, 13, 19, 36, 37, 50, 60, 99}, 47⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 37, 50, 60, 99}, 47⟩ : Position).afterPick 7 = (⟨{13, 19, 36, 37, 50, 60, 99}, 40⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_020]
  rfl

private theorem node_022 : (⟨{13, 19, 36, 37, 50, 57, 99}, 43⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_023 : (⟨{7, 13, 19, 36, 37, 50, 57, 99}, 50⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 37, 50, 57, 99}, 50⟩ : Position).afterPick 7 = (⟨{13, 19, 36, 37, 50, 57, 99}, 43⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_022]
  rfl

private theorem node_024 : (⟨{13, 19, 36, 37, 50, 57, 60}, 82⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_025 : (⟨{7, 13, 19, 36, 37, 50, 57, 60}, 89⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60}, 89⟩ : Position).afterPick 7 = (⟨{13, 19, 36, 37, 50, 57, 60}, 82⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_024]
  rfl

private theorem node_026 : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).afterPick 7 = (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_009]
    rfl
  · have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).afterPick 13 = (⟨{7, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_011]
    rfl
  · have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).afterPick 19 = (⟨{7, 13, 36, 37, 50, 57, 60, 99}, 9⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_013]
    rfl
  · have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).afterPick 36 = (⟨{7, 13, 19, 37, 50, 57, 60, 99}, 26⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_015]
    rfl
  · have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).afterPick 37 = (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_017]
    rfl
  · have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).afterPick 50 = (⟨{7, 13, 19, 36, 37, 57, 60, 99}, 40⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_019]
    rfl
  · have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).afterPick 57 = (⟨{7, 13, 19, 36, 37, 50, 60, 99}, 47⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_021]
    rfl
  · have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).afterPick 60 = (⟨{7, 13, 19, 36, 37, 50, 57, 99}, 50⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_023]
    rfl
  · have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position).afterPick 99 = (⟨{7, 13, 19, 36, 37, 50, 57, 60}, 89⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_025]
    rfl

private theorem node_027 : (⟨{4, 19, 37, 50, 57, 60, 99}, 30⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_028 : (⟨{4, 19, 36, 37, 50, 57, 60, 99}, 6⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{4, 19, 36, 37, 50, 57, 60, 99}, 6⟩ : Position).afterPick 36 = (⟨{4, 19, 37, 50, 57, 60, 99}, 30⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_027]
  rfl

private theorem node_029 : (⟨{4, 13, 37, 50, 57, 60, 99}, 24⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_030 : (⟨{4, 13, 36, 37, 50, 57, 60, 99}, 12⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{4, 13, 36, 37, 50, 57, 60, 99}, 12⟩ : Position).afterPick 36 = (⟨{4, 13, 37, 50, 57, 60, 99}, 24⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_029]
  rfl

private theorem node_031 : (⟨{13, 19, 37, 50, 57, 60, 99}, 25⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_032 : (⟨{4, 13, 19, 37, 50, 57, 60, 99}, 29⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 37, 50, 57, 60, 99}, 29⟩ : Position).afterPick 4 = (⟨{13, 19, 37, 50, 57, 60, 99}, 25⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_031]
  rfl

private theorem node_033 : (⟨{13, 19, 36, 50, 57, 60, 99}, 26⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_034 : (⟨{4, 13, 19, 36, 50, 57, 60, 99}, 30⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 36, 50, 57, 60, 99}, 30⟩ : Position).afterPick 4 = (⟨{13, 19, 36, 50, 57, 60, 99}, 26⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_033]
  rfl

private theorem node_035 : (⟨{13, 19, 36, 37, 57, 60, 99}, 39⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_036 : (⟨{4, 13, 19, 36, 37, 57, 60, 99}, 43⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 36, 37, 57, 60, 99}, 43⟩ : Position).afterPick 4 = (⟨{13, 19, 36, 37, 57, 60, 99}, 39⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_035]
  rfl

private theorem node_037 : (⟨{13, 19, 36, 37, 50, 60, 99}, 46⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_038 : (⟨{4, 13, 19, 36, 37, 50, 60, 99}, 50⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 36, 37, 50, 60, 99}, 50⟩ : Position).afterPick 4 = (⟨{13, 19, 36, 37, 50, 60, 99}, 46⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_037]
  rfl

private theorem node_039 : (⟨{13, 19, 36, 37, 50, 57, 99}, 49⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_040 : (⟨{4, 13, 19, 36, 37, 50, 57, 99}, 53⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 36, 37, 50, 57, 99}, 53⟩ : Position).afterPick 4 = (⟨{13, 19, 36, 37, 50, 57, 99}, 49⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_039]
  rfl

private theorem node_041 : (⟨{13, 19, 36, 37, 50, 57, 60}, 88⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_042 : (⟨{4, 13, 19, 36, 37, 50, 57, 60}, 92⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60}, 92⟩ : Position).afterPick 4 = (⟨{13, 19, 36, 37, 50, 57, 60}, 88⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_041]
  rfl

private theorem node_043 : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).afterPick 4 = (⟨{13, 19, 36, 37, 50, 57, 60, 99}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_009]
    rfl
  · have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).afterPick 13 = (⟨{4, 19, 36, 37, 50, 57, 60, 99}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_028]
    rfl
  · have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).afterPick 19 = (⟨{4, 13, 36, 37, 50, 57, 60, 99}, 12⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_030]
    rfl
  · have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).afterPick 36 = (⟨{4, 13, 19, 37, 50, 57, 60, 99}, 29⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_032]
    rfl
  · have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).afterPick 37 = (⟨{4, 13, 19, 36, 50, 57, 60, 99}, 30⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_034]
    rfl
  · have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).afterPick 50 = (⟨{4, 13, 19, 36, 37, 57, 60, 99}, 43⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_036]
    rfl
  · have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).afterPick 57 = (⟨{4, 13, 19, 36, 37, 50, 60, 99}, 50⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_038]
    rfl
  · have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).afterPick 60 = (⟨{4, 13, 19, 36, 37, 50, 57, 99}, 53⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_040]
    rfl
  · have he : (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position).afterPick 99 = (⟨{4, 13, 19, 36, 37, 50, 57, 60}, 92⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_042]
    rfl

private theorem node_044 : (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position).value = .loss := by
  have he : AlternatingTailObstruction.core = {4, 7, 19, 36, 37, 50, 57, 60, 99} := by decide
  simpa only [he] using AlternatingTailObstruction.core_one_loss

private theorem node_045 : (⟨{7, 13, 37, 50, 57, 60, 99}, 27⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_046 : (⟨{4, 7, 37, 50, 57, 60, 99}, 18⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

theorem node_047 : (⟨{4, 7, 13, 50, 57, 60, 99}, 6⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_048 : (⟨{4, 7, 13, 37, 57, 60, 99}, 19⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_049 : (⟨{4, 7, 13, 37, 50, 60, 99}, 26⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_050 : (⟨{4, 7, 13, 37, 50, 57, 99}, 29⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_051 : (⟨{4, 7, 13, 37, 50, 57, 60}, 68⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_052 : (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position).afterPick 4 = (⟨{7, 13, 37, 50, 57, 60, 99}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_045]
    rfl
  · have he : (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position).afterPick 7 = (⟨{4, 13, 37, 50, 57, 60, 99}, 24⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_029]
    rfl
  · have he : (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position).afterPick 13 = (⟨{4, 7, 37, 50, 57, 60, 99}, 18⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_046]
    rfl
  · have he : (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position).afterPick 37 = (⟨{4, 7, 13, 50, 57, 60, 99}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_047]
    rfl
  · have he : (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position).afterPick 50 = (⟨{4, 7, 13, 37, 57, 60, 99}, 19⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_048]
    rfl
  · have he : (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position).afterPick 57 = (⟨{4, 7, 13, 37, 50, 60, 99}, 26⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_049]
    rfl
  · have he : (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position).afterPick 60 = (⟨{4, 7, 13, 37, 50, 57, 99}, 29⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_050]
    rfl
  · have he : (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position).afterPick 99 = (⟨{4, 7, 13, 37, 50, 57, 60}, 68⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_051]
    rfl

private theorem node_053 : (⟨{4, 7, 13, 36, 37, 50, 57, 60, 99}, 5⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 36, 37, 50, 57, 60, 99}, 5⟩ : Position).afterPick 36 = (⟨{4, 7, 13, 37, 50, 57, 60, 99}, 31⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_052]
  rfl

private theorem node_054 : (⟨{7, 19, 37, 50, 57, 60, 99}, 5⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_055 : (⟨{7, 13, 19, 37, 50, 57, 60, 99}, 18⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 37, 50, 57, 60, 99}, 18⟩ : Position).afterPick 13 = (⟨{7, 19, 37, 50, 57, 60, 99}, 5⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_054]
  rfl

private theorem node_056 : (⟨{4, 7, 13, 19, 37, 50, 57, 60, 99}, 22⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 37, 50, 57, 60, 99}, 22⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 37, 50, 57, 60, 99}, 18⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_055]
  rfl

private theorem node_057 : (⟨{7, 19, 36, 50, 57, 60, 99}, 6⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_058 : (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 19⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 19⟩ : Position).afterPick 13 = (⟨{7, 19, 36, 50, 57, 60, 99}, 6⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_057]
  rfl

private theorem node_059 : (⟨{4, 7, 13, 19, 36, 50, 57, 60, 99}, 23⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 36, 50, 57, 60, 99}, 23⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 36, 50, 57, 60, 99}, 19⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_058]
  rfl

private theorem node_060 : (⟨{7, 19, 36, 37, 57, 60, 99}, 19⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_061 : (⟨{7, 13, 19, 36, 37, 57, 60, 99}, 32⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 37, 57, 60, 99}, 32⟩ : Position).afterPick 13 = (⟨{7, 19, 36, 37, 57, 60, 99}, 19⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_060]
  rfl

private theorem node_062 : (⟨{4, 7, 13, 19, 36, 37, 57, 60, 99}, 36⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 36, 37, 57, 60, 99}, 36⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 36, 37, 57, 60, 99}, 32⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_061]
  rfl

private theorem node_063 : (⟨{4, 19, 36, 37, 50, 60, 99}, 23⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_064 : (⟨{4, 13, 19, 36, 37, 50, 60, 99}, 36⟩ : Position).value = .win := by
  apply win_of_move _ _ 13 (by decide) (by decide)
  have he : (⟨{4, 13, 19, 36, 37, 50, 60, 99}, 36⟩ : Position).afterPick 13 = (⟨{4, 19, 36, 37, 50, 60, 99}, 23⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_063]
  rfl

private theorem node_065 : (⟨{4, 7, 13, 19, 36, 37, 50, 60, 99}, 43⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 36, 37, 50, 60, 99}, 43⟩ : Position).afterPick 7 = (⟨{4, 13, 19, 36, 37, 50, 60, 99}, 36⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_064]
  rfl

private theorem node_066 : (⟨{13, 19, 36, 37, 50, 57, 99}, 35⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_067 : (⟨{7, 13, 19, 36, 37, 50, 57, 99}, 42⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 37, 50, 57, 99}, 42⟩ : Position).afterPick 7 = (⟨{13, 19, 36, 37, 50, 57, 99}, 35⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_066]
  rfl

private theorem node_068 : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 99}, 46⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 99}, 46⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 36, 37, 50, 57, 99}, 42⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_067]
  rfl

private theorem node_069 : (⟨{13, 19, 36, 37, 50, 57, 60}, 74⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_070 : (⟨{7, 13, 19, 36, 37, 50, 57, 60}, 81⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 13, 19, 36, 37, 50, 57, 60}, 81⟩ : Position).afterPick 7 = (⟨{13, 19, 36, 37, 50, 57, 60}, 74⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_069]
  rfl

private theorem node_071 : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60}, 85⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60}, 85⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 36, 37, 50, 57, 60}, 81⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_070]
  rfl

private theorem node_072 : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 4 = (⟨{7, 13, 19, 36, 37, 50, 57, 60, 99}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_026]
    rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 7 = (⟨{4, 13, 19, 36, 37, 50, 57, 60, 99}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_043]
    rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 13 = (⟨{4, 7, 19, 36, 37, 50, 57, 60, 99}, 1⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_044]
    rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 19 = (⟨{4, 7, 13, 36, 37, 50, 57, 60, 99}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_053]
    rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 36 = (⟨{4, 7, 13, 19, 37, 50, 57, 60, 99}, 22⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_056]
    rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 37 = (⟨{4, 7, 13, 19, 36, 50, 57, 60, 99}, 23⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_059]
    rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 50 = (⟨{4, 7, 13, 19, 36, 37, 57, 60, 99}, 36⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_062]
    rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 57 = (⟨{4, 7, 13, 19, 36, 37, 50, 60, 99}, 43⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_065]
    rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 60 = (⟨{4, 7, 13, 19, 36, 37, 50, 57, 99}, 46⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_068]
    rfl
  · have he : (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60, 99}, 14⟩ : Position).afterPick 99 = (⟨{4, 7, 13, 19, 36, 37, 50, 57, 60}, 85⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_071]
    rfl

def support : Finset ℕ := {4, 7, 13, 19, 36, 37, 50, 57, 60, 99}

theorem parent_loss : (⟨support, 14⟩ : Position).value = .loss :=
  node_072

/-- Inserting the guard can turn a loss at a larger deficit into a win. -/
def inserted : Finset ℕ := insert 2 support

/-- A unit-deficit source whose winning move will fail when the guard is added. -/
def winningSource : Finset ℕ := insert 15 support

def guardedSource : Finset ℕ := insert 2 winningSource

theorem inserted_after_thirteen :
    (⟨inserted, 14⟩ : Position).afterPick 13 =
      (⟨insert 2 AlternatingTailObstruction.core, 1⟩ : Position) := by
  decide +kernel

theorem core_guard_win :
    (⟨insert 2 AlternatingTailObstruction.core, 1⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨insert 2 AlternatingTailObstruction.core, 1⟩ : Position).afterPick 2 =
      (⟨AlternatingTailObstruction.core, 1⟩ : Position) := by decide
  rw [Position.moveOutcome, he, AlternatingTailObstruction.core_one_loss]
  rfl

theorem inserted_move_thirteen :
    (⟨inserted, 14⟩ : Position).moveOutcome 13 = .win := by
  rw [Position.moveOutcome, inserted_after_thirteen, core_guard_win]
  rfl

theorem inserted_win : (⟨inserted, 14⟩ : Position).value = .win := by
  exact win_of_move _ _ 13 (by decide) (by decide) inserted_move_thirteen

theorem arithmetic_premises :
    support.card = 10 ∧ support.sum id = 382 ∧
      Even (14 + support.sum id) ∧ 2 ≤ 14 ∧
      (∀ x ∈ support, 3 ≤ x) ∧ 14 ≤ support.sum id ∧ 14 - 1 ∈ support ∧
      inserted.card = 11 ∧ inserted.sum id = 384 ∧
      Even (14 + inserted.sum id) := by
  decide +kernel

theorem source_geometry :
    winningSource.card = 11 ∧ winningSource.sum id = 397 ∧
      guardedSource.card = 12 ∧ guardedSource.sum id = 399 ∧
      Odd (winningSource.sum id) ∧ Odd (guardedSource.sum id) ∧
      (∀ x ∈ winningSource, 3 ≤ x) ∧ (∀ x ∈ guardedSource, 2 ≤ x) ∧
      2 ∈ guardedSource ∧ guardedSource.erase 2 = winningSource ∧
      15 ∈ winningSource ∧ 15 ∈ guardedSource := by
  decide +kernel

theorem every_pick_loses (x : ℕ) (hx : x ∈ support) :
    (⟨support, 14⟩ : Position).moveOutcome x = .loss := by
  exact (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mp
    parent_loss x hx

theorem winningSource_after_fifteen :
    (⟨winningSource, 1⟩ : Position).afterPick 15 = (⟨support, 14⟩ : Position) := by
  decide +kernel

theorem guardedSource_after_fifteen :
    (⟨guardedSource, 1⟩ : Position).afterPick 15 = (⟨inserted, 14⟩ : Position) := by
  decide +kernel

theorem winningSource_move_fifteen :
    (⟨winningSource, 1⟩ : Position).moveOutcome 15 = .win := by
  simp [Position.moveOutcome, winningSource_after_fifteen, parent_loss, Outcome.neg]

theorem guardedSource_move_fifteen :
    (⟨guardedSource, 1⟩ : Position).moveOutcome 15 = .loss := by
  simp [Position.moveOutcome, guardedSource_after_fifteen, inserted_win, Outcome.neg]

theorem winningSource_win : (⟨winningSource, 1⟩ : Position).value = .win := by
  exact win_of_move _ _ 15 (by decide) (by decide) winningSource_move_fifteen

theorem not_near_deficit_nonloss :
    ¬ (∀ (S : Finset ℕ) (d : ℕ), 2 ≤ d → (∀ x ∈ S, 3 ≤ x) →
      Even (d + S.sum id) → d ≤ S.sum id → d - 1 ∈ S →
      (⟨S, d⟩ : Position).value ≠ .loss) := by
  intro h
  exact h support 14 (by decide) (by decide) (by decide) (by decide) (by decide)
    parent_loss

theorem not_insert_two_nonwin :
    ¬ (∀ (S : Finset ℕ) (d : ℕ), 2 ≤ d → (∀ x ∈ S, 3 ≤ x) →
      Even (d + S.sum id) → d ≤ S.sum id → d - 1 ∈ S →
      (⟨S, d⟩ : Position).value = .loss →
      (⟨insert 2 S, d⟩ : Position).value ≠ .win) := by
  intro h
  exact h support 14 (by decide) (by decide) (by decide) (by decide) (by decide)
    parent_loss inserted_win

theorem not_copy_winning_move :
    ¬ (∀ (S : Finset ℕ) (x : ℕ), (∀ y ∈ S, 3 ≤ y) → Odd (S.sum id) →
      x ∈ S → (⟨S, 1⟩ : Position).moveOutcome x = .win →
      (⟨insert 2 S, 1⟩ : Position).moveOutcome x ≠ .loss) := by
  intro h
  exact h winningSource 15 (by decide) (by decide) (by decide)
    winningSource_move_fifteen guardedSource_move_fifteen

/- The guarded source's complete value and uniqueness of safe moves are not
asserted here. These theorems refute the proposed transfer of a particular
winning move; they do not refute the unit-deficit guard conjecture or the
initial-interval Catch-Up conjecture. -/


end CatchUp.NearDeficitGuardObstruction
