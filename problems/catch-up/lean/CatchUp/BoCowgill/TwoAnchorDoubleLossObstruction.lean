/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/TwoAnchorDoubleLossObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DeficitTwo
public import CatchUp.BoCowgill.WinningOpening

/-!
# A sparse obstruction to the unrestricted two-anchor double-loss claim

The generated private proof DAG shares exact W/L subpositions. Every LOSS node
covers every legal pick; every WIN node supplies one legal winning pick.
Small leaves replay the proved executable evaluator in the kernel.
This is not a counterexample to the interval conjecture or the anchor-eight claim.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.TwoAnchorDoubleLossObstruction

open CatchUp (Position.value_eq_loss_iff_of_nonterminal)
open CatchUp.DeficitTwo (win_of_move)

private theorem node_001 : (⟨{35, 36, 52, 56, 62, 74, 100}, 5⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_002 : (⟨{18, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_003 : (⟨{18, 35, 52, 56, 62, 74, 100}, 13⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_004 : (⟨{18, 35, 36, 56, 62, 74, 100}, 29⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_005 : (⟨{18, 35, 36, 52, 62, 74, 100}, 33⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_006 : (⟨{18, 35, 36, 52, 56, 74, 100}, 39⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_007 : (⟨{18, 35, 36, 52, 56, 62, 100}, 51⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_008 : (⟨{18, 35, 36, 52, 56, 62, 74}, 77⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_009 : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).afterPick 18 = (⟨{35, 36, 52, 56, 62, 74, 100}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_001]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).afterPick 35 = (⟨{18, 36, 52, 56, 62, 74, 100}, 12⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_002]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).afterPick 36 = (⟨{18, 35, 52, 56, 62, 74, 100}, 13⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_003]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).afterPick 52 = (⟨{18, 35, 36, 56, 62, 74, 100}, 29⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_004]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).afterPick 56 = (⟨{18, 35, 36, 52, 62, 74, 100}, 33⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_005]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).afterPick 62 = (⟨{18, 35, 36, 52, 56, 74, 100}, 39⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_006]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).afterPick 74 = (⟨{18, 35, 36, 52, 56, 62, 100}, 51⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_007]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).afterPick 100 = (⟨{18, 35, 36, 52, 56, 62, 74}, 77⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_008]
    rfl

private theorem node_010 : (⟨{7, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_011 : (⟨{7, 35, 52, 56, 62, 74, 100}, 24⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_012 : (⟨{7, 35, 36, 56, 62, 74, 100}, 40⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_013 : (⟨{7, 35, 36, 52, 62, 74, 100}, 44⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_014 : (⟨{7, 35, 36, 52, 56, 74, 100}, 50⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_015 : (⟨{7, 35, 36, 52, 56, 62, 100}, 62⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_016 : (⟨{7, 35, 36, 52, 56, 62, 74}, 88⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_017 : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).afterPick 7 = (⟨{35, 36, 52, 56, 62, 74, 100}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_001]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).afterPick 35 = (⟨{7, 36, 52, 56, 62, 74, 100}, 23⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_010]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).afterPick 36 = (⟨{7, 35, 52, 56, 62, 74, 100}, 24⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_011]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).afterPick 52 = (⟨{7, 35, 36, 56, 62, 74, 100}, 40⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_012]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).afterPick 56 = (⟨{7, 35, 36, 52, 62, 74, 100}, 44⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_013]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).afterPick 62 = (⟨{7, 35, 36, 52, 56, 74, 100}, 50⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_014]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).afterPick 74 = (⟨{7, 35, 36, 52, 56, 62, 100}, 62⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_015]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position).afterPick 100 = (⟨{7, 35, 36, 52, 56, 62, 74}, 88⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_016]
    rfl

private theorem node_018 : (⟨{18, 36, 52, 56, 62, 74, 100}, 2⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_019 : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 5⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 5⟩ : Position).afterPick 7 = (⟨{18, 36, 52, 56, 62, 74, 100}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_018]
  rfl

private theorem node_020 : (⟨{18, 35, 52, 56, 62, 74, 100}, 1⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_021 : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 6⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 6⟩ : Position).afterPick 7 = (⟨{18, 35, 52, 56, 62, 74, 100}, 1⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_020]
  rfl

private theorem node_022 : (⟨{7, 35, 36, 56, 62, 74, 100}, 4⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_023 : (⟨{7, 18, 35, 36, 56, 62, 74, 100}, 22⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 56, 62, 74, 100}, 22⟩ : Position).afterPick 18 = (⟨{7, 35, 36, 56, 62, 74, 100}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_022]
  rfl

private theorem node_024 : (⟨{18, 35, 36, 52, 62, 74, 100}, 19⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_025 : (⟨{7, 18, 35, 36, 52, 62, 74, 100}, 26⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 62, 74, 100}, 26⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 62, 74, 100}, 19⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_024]
  rfl

private theorem node_026 : (⟨{18, 35, 36, 52, 56, 74, 100}, 25⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_027 : (⟨{7, 18, 35, 36, 52, 56, 74, 100}, 32⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 74, 100}, 32⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 56, 74, 100}, 25⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_026]
  rfl

private theorem node_028 : (⟨{18, 35, 36, 52, 56, 62, 100}, 37⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_029 : (⟨{7, 18, 35, 36, 52, 56, 62, 100}, 44⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 62, 100}, 44⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 56, 62, 100}, 37⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_028]
  rfl

private theorem node_030 : (⟨{18, 35, 36, 52, 56, 62, 74}, 63⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_031 : (⟨{7, 18, 35, 36, 52, 56, 62, 74}, 70⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74}, 70⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 56, 62, 74}, 63⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_030]
  rfl

private theorem node_032 : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_009]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 18 = (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_017]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 35 = (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_019]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 36 = (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_021]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 52 = (⟨{7, 18, 35, 36, 56, 62, 74, 100}, 22⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_023]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 56 = (⟨{7, 18, 35, 36, 52, 62, 74, 100}, 26⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_025]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 62 = (⟨{7, 18, 35, 36, 52, 56, 74, 100}, 32⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_027]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 74 = (⟨{7, 18, 35, 36, 52, 56, 62, 100}, 44⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_029]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 100 = (⟨{7, 18, 35, 36, 52, 56, 62, 74}, 70⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_031]
    rfl

private theorem node_033 : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).value = .win := by
  apply win_of_move _ _ 33 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 33 = (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_032]
  rfl

private theorem node_034 : (⟨{4, 36, 52, 56, 62, 74, 100}, 26⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_035 : (⟨{4, 35, 52, 56, 62, 74, 100}, 27⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_036 : (⟨{4, 35, 36, 56, 62, 74, 100}, 43⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_037 : (⟨{4, 35, 36, 52, 62, 74, 100}, 47⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_038 : (⟨{4, 35, 36, 52, 56, 74, 100}, 53⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_039 : (⟨{4, 35, 36, 52, 56, 62, 100}, 65⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_040 : (⟨{4, 35, 36, 52, 56, 62, 74}, 91⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_041 : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 4 = (⟨{35, 36, 52, 56, 62, 74, 100}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_001]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 35 = (⟨{4, 36, 52, 56, 62, 74, 100}, 26⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_034]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 36 = (⟨{4, 35, 52, 56, 62, 74, 100}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_035]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 52 = (⟨{4, 35, 36, 56, 62, 74, 100}, 43⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_036]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 56 = (⟨{4, 35, 36, 52, 62, 74, 100}, 47⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_037]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 62 = (⟨{4, 35, 36, 52, 56, 74, 100}, 53⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_038]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 74 = (⟨{4, 35, 36, 52, 56, 62, 100}, 65⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_039]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 100 = (⟨{4, 35, 36, 52, 56, 62, 74}, 91⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_040]
    rfl

private theorem node_042 : (⟨{18, 36, 52, 56, 62, 74, 100}, 4⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_043 : (⟨{4, 18, 36, 52, 56, 62, 74, 100}, 8⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 36, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 4 = (⟨{18, 36, 52, 56, 62, 74, 100}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_042]
  rfl

private theorem node_044 : (⟨{18, 35, 52, 56, 62, 74, 100}, 5⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_045 : (⟨{4, 18, 35, 52, 56, 62, 74, 100}, 9⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 4 = (⟨{18, 35, 52, 56, 62, 74, 100}, 5⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_044]
  rfl

private theorem node_046 : (⟨{18, 35, 36, 56, 62, 74, 100}, 21⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_047 : (⟨{4, 18, 35, 36, 56, 62, 74, 100}, 25⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 56, 62, 74, 100}, 25⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 56, 62, 74, 100}, 21⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_046]
  rfl

private theorem node_048 : (⟨{18, 35, 36, 52, 62, 74, 100}, 25⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_049 : (⟨{4, 18, 35, 36, 52, 62, 74, 100}, 29⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 52, 62, 74, 100}, 29⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 62, 74, 100}, 25⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_048]
  rfl

private theorem node_050 : (⟨{18, 35, 36, 52, 56, 74, 100}, 31⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_051 : (⟨{4, 18, 35, 36, 52, 56, 74, 100}, 35⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 52, 56, 74, 100}, 35⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 56, 74, 100}, 31⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_050]
  rfl

private theorem node_052 : (⟨{18, 35, 36, 52, 56, 62, 100}, 43⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_053 : (⟨{4, 18, 35, 36, 52, 56, 62, 100}, 47⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 52, 56, 62, 100}, 47⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 56, 62, 100}, 43⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_052]
  rfl

private theorem node_054 : (⟨{18, 35, 36, 52, 56, 62, 74}, 69⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_055 : (⟨{4, 18, 35, 36, 52, 56, 62, 74}, 73⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74}, 73⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 56, 62, 74}, 69⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_054]
  rfl

private theorem node_056 : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_009]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).afterPick 18 = (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_041]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).afterPick 35 = (⟨{4, 18, 36, 52, 56, 62, 74, 100}, 8⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_043]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).afterPick 36 = (⟨{4, 18, 35, 52, 56, 62, 74, 100}, 9⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_045]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).afterPick 52 = (⟨{4, 18, 35, 36, 56, 62, 74, 100}, 25⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_047]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).afterPick 56 = (⟨{4, 18, 35, 36, 52, 62, 74, 100}, 29⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_049]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).afterPick 62 = (⟨{4, 18, 35, 36, 52, 56, 74, 100}, 35⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_051]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).afterPick 74 = (⟨{4, 18, 35, 36, 52, 56, 62, 100}, 47⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_053]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position).afterPick 100 = (⟨{4, 18, 35, 36, 52, 56, 62, 74}, 73⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_055]
    rfl

private theorem node_057 : (⟨{4, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 6⟩ : Position).value = .win := by
  apply win_of_move _ _ 33 (by decide) (by decide)
  have he : (⟨{4, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 6⟩ : Position).afterPick 33 = (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 27⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_056]
  rfl

private theorem node_058 : (⟨{7, 36, 52, 56, 62, 74, 100}, 15⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_059 : (⟨{4, 7, 36, 52, 56, 62, 74, 100}, 19⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 36, 52, 56, 62, 74, 100}, 19⟩ : Position).afterPick 4 = (⟨{7, 36, 52, 56, 62, 74, 100}, 15⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_058]
  rfl

private theorem node_060 : (⟨{7, 35, 52, 56, 62, 74, 100}, 16⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_061 : (⟨{4, 7, 35, 52, 56, 62, 74, 100}, 20⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 35, 52, 56, 62, 74, 100}, 20⟩ : Position).afterPick 4 = (⟨{7, 35, 52, 56, 62, 74, 100}, 16⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_060]
  rfl

private theorem node_062 : (⟨{7, 35, 36, 56, 62, 74, 100}, 32⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_063 : (⟨{4, 7, 35, 36, 56, 62, 74, 100}, 36⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 35, 36, 56, 62, 74, 100}, 36⟩ : Position).afterPick 4 = (⟨{7, 35, 36, 56, 62, 74, 100}, 32⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_062]
  rfl

private theorem node_064 : (⟨{7, 35, 36, 52, 62, 74, 100}, 36⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_065 : (⟨{4, 7, 35, 36, 52, 62, 74, 100}, 40⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 35, 36, 52, 62, 74, 100}, 40⟩ : Position).afterPick 4 = (⟨{7, 35, 36, 52, 62, 74, 100}, 36⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_064]
  rfl

private theorem node_066 : (⟨{4, 7, 35, 36, 52, 56, 100}, 28⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_067 : (⟨{4, 7, 35, 36, 52, 56, 74, 100}, 46⟩ : Position).value = .win := by
  apply win_of_move _ _ 74 (by decide) (by decide)
  have he : (⟨{4, 7, 35, 36, 52, 56, 74, 100}, 46⟩ : Position).afterPick 74 = (⟨{4, 7, 35, 36, 52, 56, 100}, 28⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_066]
  rfl

private theorem node_068 : (⟨{7, 35, 36, 52, 56, 62, 100}, 54⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_069 : (⟨{4, 7, 35, 36, 52, 56, 62, 100}, 58⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 35, 36, 52, 56, 62, 100}, 58⟩ : Position).afterPick 4 = (⟨{7, 35, 36, 52, 56, 62, 100}, 54⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_068]
  rfl

private theorem node_070 : (⟨{7, 35, 36, 52, 56, 62, 74}, 80⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_071 : (⟨{4, 7, 35, 36, 52, 56, 62, 74}, 84⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74}, 84⟩ : Position).afterPick 4 = (⟨{7, 35, 36, 52, 56, 62, 74}, 80⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_070]
  rfl

private theorem node_072 : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).afterPick 4 = (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_017]
    rfl
  · have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).afterPick 7 = (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 9⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_041]
    rfl
  · have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).afterPick 35 = (⟨{4, 7, 36, 52, 56, 62, 74, 100}, 19⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_059]
    rfl
  · have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).afterPick 36 = (⟨{4, 7, 35, 52, 56, 62, 74, 100}, 20⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_061]
    rfl
  · have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).afterPick 52 = (⟨{4, 7, 35, 36, 56, 62, 74, 100}, 36⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_063]
    rfl
  · have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).afterPick 56 = (⟨{4, 7, 35, 36, 52, 62, 74, 100}, 40⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_065]
    rfl
  · have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).afterPick 62 = (⟨{4, 7, 35, 36, 52, 56, 74, 100}, 46⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_067]
    rfl
  · have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).afterPick 74 = (⟨{4, 7, 35, 36, 52, 56, 62, 100}, 58⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_069]
    rfl
  · have he : (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position).afterPick 100 = (⟨{4, 7, 35, 36, 52, 56, 62, 74}, 84⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_071]
    rfl

private theorem node_073 : (⟨{4, 7, 33, 35, 36, 52, 56, 62, 74, 100}, 17⟩ : Position).value = .win := by
  apply win_of_move _ _ 33 (by decide) (by decide)
  have he : (⟨{4, 7, 33, 35, 36, 52, 56, 62, 74, 100}, 17⟩ : Position).afterPick 33 = (⟨{4, 7, 35, 36, 52, 56, 62, 74, 100}, 16⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_072]
  rfl

private theorem node_074 : (⟨{7, 35, 52, 56, 62, 74, 100}, 10⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_075 : (⟨{7, 18, 52, 56, 62, 74, 100}, 27⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_076 : (⟨{7, 18, 35, 56, 62, 74, 100}, 44⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_077 : (⟨{7, 18, 35, 52, 62, 74, 100}, 48⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_078 : (⟨{7, 18, 35, 52, 56, 74, 100}, 54⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_079 : (⟨{7, 18, 35, 52, 56, 62, 100}, 66⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_080 : (⟨{7, 18, 35, 52, 56, 62, 74}, 92⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_081 : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 7 = (⟨{18, 35, 52, 56, 62, 74, 100}, 1⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_020]
    rfl
  · have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 18 = (⟨{7, 35, 52, 56, 62, 74, 100}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_074]
    rfl
  · have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 35 = (⟨{7, 18, 52, 56, 62, 74, 100}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_075]
    rfl
  · have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 52 = (⟨{7, 18, 35, 56, 62, 74, 100}, 44⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_076]
    rfl
  · have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 56 = (⟨{7, 18, 35, 52, 62, 74, 100}, 48⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_077]
    rfl
  · have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 62 = (⟨{7, 18, 35, 52, 56, 74, 100}, 54⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_078]
    rfl
  · have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 74 = (⟨{7, 18, 35, 52, 56, 62, 100}, 66⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_079]
    rfl
  · have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 100 = (⟨{7, 18, 35, 52, 56, 62, 74}, 92⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_080]
    rfl

private theorem node_082 : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 28⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 28⟩ : Position).afterPick 36 = (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 8⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_081]
  rfl

private theorem node_083 : (⟨{4, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 4 = (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 28⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_082]
  rfl

private theorem node_084 : (⟨{18, 33, 52, 56, 62, 74, 100}, 13⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_085 : (⟨{18, 33, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{18, 33, 36, 52, 56, 62, 74, 100}, 23⟩ : Position).afterPick 36 = (⟨{18, 33, 52, 56, 62, 74, 100}, 13⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_084]
  rfl

private theorem node_086 : (⟨{7, 18, 33, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 7 = (⟨{18, 33, 36, 52, 56, 62, 74, 100}, 23⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_085]
  rfl

private theorem node_087 : (⟨{4, 7, 18, 33, 36, 52, 56, 62, 74, 100}, 34⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 36, 52, 56, 62, 74, 100}, 34⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 36, 52, 56, 62, 74, 100}, 30⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_086]
  rfl

private theorem node_088 : (⟨{4, 33, 35, 56, 62, 74, 100}, 42⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_089 : (⟨{4, 33, 35, 52, 56, 62, 74, 100}, 10⟩ : Position).value = .win := by
  apply win_of_move _ _ 52 (by decide) (by decide)
  have he : (⟨{4, 33, 35, 52, 56, 62, 74, 100}, 10⟩ : Position).afterPick 52 = (⟨{4, 33, 35, 56, 62, 74, 100}, 42⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_088]
  rfl

private theorem node_090 : (⟨{4, 18, 33, 35, 52, 56, 62, 74, 100}, 28⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{4, 18, 33, 35, 52, 56, 62, 74, 100}, 28⟩ : Position).afterPick 18 = (⟨{4, 33, 35, 52, 56, 62, 74, 100}, 10⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_089]
  rfl

private theorem node_091 : (⟨{4, 7, 18, 33, 35, 52, 56, 62, 74, 100}, 35⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 52, 56, 62, 74, 100}, 35⟩ : Position).afterPick 7 = (⟨{4, 18, 33, 35, 52, 56, 62, 74, 100}, 28⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_090]
  rfl

private theorem node_092 : (⟨{18, 33, 35, 56, 62, 74, 100}, 4⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_093 : (⟨{18, 33, 35, 36, 56, 62, 74, 100}, 40⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 36, 56, 62, 74, 100}, 40⟩ : Position).afterPick 36 = (⟨{18, 33, 35, 56, 62, 74, 100}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_092]
  rfl

private theorem node_094 : (⟨{7, 18, 33, 35, 36, 56, 62, 74, 100}, 47⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 56, 62, 74, 100}, 47⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 36, 56, 62, 74, 100}, 40⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_093]
  rfl

private theorem node_095 : (⟨{4, 7, 18, 33, 35, 36, 56, 62, 74, 100}, 51⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 56, 62, 74, 100}, 51⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 56, 62, 74, 100}, 47⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_094]
  rfl

private theorem node_096 : (⟨{33, 35, 36, 52, 62, 74, 100}, 26⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_097 : (⟨{18, 33, 35, 36, 52, 62, 74, 100}, 44⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 36, 52, 62, 74, 100}, 44⟩ : Position).afterPick 18 = (⟨{33, 35, 36, 52, 62, 74, 100}, 26⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_096]
  rfl

private theorem node_098 : (⟨{7, 18, 33, 35, 36, 52, 62, 74, 100}, 51⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 62, 74, 100}, 51⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 36, 52, 62, 74, 100}, 44⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_097]
  rfl

private theorem node_099 : (⟨{4, 7, 18, 33, 35, 36, 52, 62, 74, 100}, 55⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 52, 62, 74, 100}, 55⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 62, 74, 100}, 51⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_098]
  rfl

private theorem node_100 : (⟨{33, 35, 36, 52, 56, 74, 100}, 32⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_101 : (⟨{18, 33, 35, 36, 52, 56, 74, 100}, 50⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 36, 52, 56, 74, 100}, 50⟩ : Position).afterPick 18 = (⟨{33, 35, 36, 52, 56, 74, 100}, 32⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_100]
  rfl

private theorem node_102 : (⟨{7, 18, 33, 35, 36, 52, 56, 74, 100}, 57⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 56, 74, 100}, 57⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 36, 52, 56, 74, 100}, 50⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_101]
  rfl

private theorem node_103 : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 74, 100}, 61⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 74, 100}, 61⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 56, 74, 100}, 57⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_102]
  rfl

private theorem node_104 : (⟨{33, 35, 36, 52, 56, 62, 100}, 44⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_105 : (⟨{18, 33, 35, 36, 52, 56, 62, 100}, 62⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 36, 52, 56, 62, 100}, 62⟩ : Position).afterPick 18 = (⟨{33, 35, 36, 52, 56, 62, 100}, 44⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_104]
  rfl

private theorem node_106 : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 100}, 69⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 100}, 69⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 36, 52, 56, 62, 100}, 62⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_105]
  rfl

private theorem node_107 : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 100}, 73⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 100}, 73⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 56, 62, 100}, 69⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_106]
  rfl

private theorem node_108 : (⟨{33, 35, 36, 52, 56, 62, 74}, 70⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_109 : (⟨{18, 33, 35, 36, 52, 56, 62, 74}, 88⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 36, 52, 56, 62, 74}, 88⟩ : Position).afterPick 18 = (⟨{33, 35, 36, 52, 56, 62, 74}, 70⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_108]
  rfl

private theorem node_110 : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74}, 95⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74}, 95⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 36, 52, 56, 62, 74}, 88⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_109]
  rfl

private theorem node_111 : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74}, 99⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74}, 99⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74}, 95⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_110]
  rfl

private theorem node_112 : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_033]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 7 = (⟨{4, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_057]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 18 = (⟨{4, 7, 33, 35, 36, 52, 56, 62, 74, 100}, 17⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_073]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 33 = (⟨{4, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_083]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 35 = (⟨{4, 7, 18, 33, 36, 52, 56, 62, 74, 100}, 34⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_087]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 36 = (⟨{4, 7, 18, 33, 35, 52, 56, 62, 74, 100}, 35⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_091]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 52 = (⟨{4, 7, 18, 33, 35, 36, 56, 62, 74, 100}, 51⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_095]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 56 = (⟨{4, 7, 18, 33, 35, 36, 52, 62, 74, 100}, 55⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_099]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 62 = (⟨{4, 7, 18, 33, 35, 36, 52, 56, 74, 100}, 61⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_103]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 74 = (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 100}, 73⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_107]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 100 = (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74}, 99⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_111]
    rfl

private theorem node_113 : (⟨{35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_114 : (⟨{18, 36, 52, 56, 62, 74, 100}, 10⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_115 : (⟨{18, 35, 52, 56, 62, 74, 100}, 11⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_116 : (⟨{18, 35, 36, 56, 62, 74, 100}, 27⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_117 : (⟨{18, 35, 36, 52, 62, 74, 100}, 31⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_118 : (⟨{18, 35, 36, 52, 56, 74, 100}, 37⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_119 : (⟨{18, 35, 36, 52, 56, 62, 100}, 49⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_120 : (⟨{18, 35, 36, 52, 56, 62, 74}, 75⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_121 : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 18 = (⟨{35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_113]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 35 = (⟨{18, 36, 52, 56, 62, 74, 100}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_114]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 36 = (⟨{18, 35, 52, 56, 62, 74, 100}, 11⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_115]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 52 = (⟨{18, 35, 36, 56, 62, 74, 100}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_116]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 56 = (⟨{18, 35, 36, 52, 62, 74, 100}, 31⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_117]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 62 = (⟨{18, 35, 36, 52, 56, 74, 100}, 37⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_118]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 74 = (⟨{18, 35, 36, 52, 56, 62, 100}, 49⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_119]
    rfl
  · have he : (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 100 = (⟨{18, 35, 36, 52, 56, 62, 74}, 75⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_120]
    rfl

private theorem node_122 : (⟨{7, 36, 52, 56, 62, 74, 100}, 21⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_123 : (⟨{7, 35, 52, 56, 62, 74, 100}, 22⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_124 : (⟨{7, 35, 36, 56, 62, 74, 100}, 38⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_125 : (⟨{7, 35, 36, 52, 62, 74, 100}, 42⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_126 : (⟨{7, 35, 36, 52, 56, 74, 100}, 48⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_127 : (⟨{7, 35, 36, 52, 56, 62, 100}, 60⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_128 : (⟨{7, 35, 36, 52, 56, 62, 74}, 86⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_129 : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 7 = (⟨{35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_113]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 35 = (⟨{7, 36, 52, 56, 62, 74, 100}, 21⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_122]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 36 = (⟨{7, 35, 52, 56, 62, 74, 100}, 22⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_123]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 52 = (⟨{7, 35, 36, 56, 62, 74, 100}, 38⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_124]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 56 = (⟨{7, 35, 36, 52, 62, 74, 100}, 42⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_125]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 62 = (⟨{7, 35, 36, 52, 56, 74, 100}, 48⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_126]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 74 = (⟨{7, 35, 36, 52, 56, 62, 100}, 60⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_127]
    rfl
  · have he : (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 100 = (⟨{7, 35, 36, 52, 56, 62, 74}, 86⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_128]
    rfl

private theorem node_130 : (⟨{7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_131 : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 36 = (⟨{7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_130]
  rfl

private theorem node_132 : (⟨{7, 18, 52, 56, 62, 74, 100}, 31⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_133 : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 4⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 4⟩ : Position).afterPick 35 = (⟨{7, 18, 52, 56, 62, 74, 100}, 31⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_132]
  rfl

private theorem node_134 : (⟨{7, 35, 36, 56, 62, 74, 100}, 2⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_135 : (⟨{7, 18, 35, 36, 56, 62, 74, 100}, 20⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 56, 62, 74, 100}, 20⟩ : Position).afterPick 18 = (⟨{7, 35, 36, 56, 62, 74, 100}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_134]
  rfl

private theorem node_136 : (⟨{7, 35, 36, 52, 62, 74, 100}, 6⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_137 : (⟨{7, 18, 35, 36, 52, 62, 74, 100}, 24⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 62, 74, 100}, 24⟩ : Position).afterPick 18 = (⟨{7, 35, 36, 52, 62, 74, 100}, 6⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_136]
  rfl

private theorem node_138 : (⟨{7, 35, 36, 52, 56, 74, 100}, 12⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_139 : (⟨{7, 18, 35, 36, 52, 56, 74, 100}, 30⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 74, 100}, 30⟩ : Position).afterPick 18 = (⟨{7, 35, 36, 52, 56, 74, 100}, 12⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_138]
  rfl

private theorem node_140 : (⟨{7, 35, 36, 52, 56, 62, 100}, 24⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_141 : (⟨{7, 18, 35, 36, 52, 56, 62, 100}, 42⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 62, 100}, 42⟩ : Position).afterPick 18 = (⟨{7, 35, 36, 52, 56, 62, 100}, 24⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_140]
  rfl

private theorem node_142 : (⟨{18, 35, 36, 52, 56, 62, 74}, 61⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_143 : (⟨{7, 18, 35, 36, 52, 56, 62, 74}, 68⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74}, 68⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 56, 62, 74}, 61⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_142]
  rfl

private theorem node_144 : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_121]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 18 = (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_129]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 35 = (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_131]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 36 = (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 4⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_133]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 52 = (⟨{7, 18, 35, 36, 56, 62, 74, 100}, 20⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_135]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 56 = (⟨{7, 18, 35, 36, 52, 62, 74, 100}, 24⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_137]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 62 = (⟨{7, 18, 35, 36, 52, 56, 74, 100}, 30⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_139]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 74 = (⟨{7, 18, 35, 36, 52, 56, 62, 100}, 42⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_141]
    rfl
  · have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 100 = (⟨{7, 18, 35, 36, 52, 56, 62, 74}, 68⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_143]
    rfl

private theorem node_145 : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).value = .win := by
  apply win_of_move _ _ 33 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 33 = (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_144]
  rfl

private theorem node_146 : (⟨{4, 36, 52, 56, 62, 74, 100}, 24⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_147 : (⟨{4, 35, 52, 56, 62, 74, 100}, 25⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_148 : (⟨{4, 35, 36, 56, 62, 74, 100}, 41⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_149 : (⟨{4, 35, 36, 52, 62, 74, 100}, 45⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_150 : (⟨{4, 35, 36, 52, 56, 74, 100}, 51⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_151 : (⟨{4, 35, 36, 52, 56, 62, 100}, 63⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_152 : (⟨{4, 35, 36, 52, 56, 62, 74}, 89⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_153 : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 4 = (⟨{35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_113]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 35 = (⟨{4, 36, 52, 56, 62, 74, 100}, 24⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_146]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 36 = (⟨{4, 35, 52, 56, 62, 74, 100}, 25⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_147]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 52 = (⟨{4, 35, 36, 56, 62, 74, 100}, 41⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_148]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 56 = (⟨{4, 35, 36, 52, 62, 74, 100}, 45⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_149]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 62 = (⟨{4, 35, 36, 52, 56, 74, 100}, 51⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_150]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 74 = (⟨{4, 35, 36, 52, 56, 62, 100}, 63⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_151]
    rfl
  · have he : (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 100 = (⟨{4, 35, 36, 52, 56, 62, 74}, 89⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_152]
    rfl

private theorem node_154 : (⟨{4, 18, 52, 56, 62, 74, 100}, 30⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_155 : (⟨{4, 18, 36, 52, 56, 62, 74, 100}, 6⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{4, 18, 36, 52, 56, 62, 74, 100}, 6⟩ : Position).afterPick 36 = (⟨{4, 18, 52, 56, 62, 74, 100}, 30⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_154]
  rfl

private theorem node_156 : (⟨{18, 35, 52, 56, 62, 74, 100}, 3⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_157 : (⟨{4, 18, 35, 52, 56, 62, 74, 100}, 7⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 52, 56, 62, 74, 100}, 7⟩ : Position).afterPick 4 = (⟨{18, 35, 52, 56, 62, 74, 100}, 3⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_156]
  rfl

private theorem node_158 : (⟨{18, 35, 36, 56, 62, 74, 100}, 19⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_159 : (⟨{4, 18, 35, 36, 56, 62, 74, 100}, 23⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 56, 62, 74, 100}, 23⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 56, 62, 74, 100}, 19⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_158]
  rfl

private theorem node_160 : (⟨{18, 35, 36, 52, 62, 74, 100}, 23⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_161 : (⟨{4, 18, 35, 36, 52, 62, 74, 100}, 27⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 52, 62, 74, 100}, 27⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 62, 74, 100}, 23⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_160]
  rfl

private theorem node_162 : (⟨{18, 35, 36, 52, 56, 74, 100}, 29⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_163 : (⟨{4, 18, 35, 36, 52, 56, 74, 100}, 33⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 52, 56, 74, 100}, 33⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 56, 74, 100}, 29⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_162]
  rfl

private theorem node_164 : (⟨{18, 35, 36, 52, 56, 62, 100}, 41⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_165 : (⟨{4, 18, 35, 36, 52, 56, 62, 100}, 45⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 52, 56, 62, 100}, 45⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 56, 62, 100}, 41⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_164]
  rfl

private theorem node_166 : (⟨{18, 35, 36, 52, 56, 62, 74}, 67⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_167 : (⟨{4, 18, 35, 36, 52, 56, 62, 74}, 71⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74}, 71⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 56, 62, 74}, 67⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_166]
  rfl

private theorem node_168 : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 4 = (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_121]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 18 = (⟨{4, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_153]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 35 = (⟨{4, 18, 36, 52, 56, 62, 74, 100}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_155]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 36 = (⟨{4, 18, 35, 52, 56, 62, 74, 100}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_157]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 52 = (⟨{4, 18, 35, 36, 56, 62, 74, 100}, 23⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_159]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 56 = (⟨{4, 18, 35, 36, 52, 62, 74, 100}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_161]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 62 = (⟨{4, 18, 35, 36, 52, 56, 74, 100}, 33⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_163]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 74 = (⟨{4, 18, 35, 36, 52, 56, 62, 100}, 45⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_165]
    rfl
  · have he : (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 100 = (⟨{4, 18, 35, 36, 52, 56, 62, 74}, 71⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_167]
    rfl

private theorem node_169 : (⟨{4, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 4⟩ : Position).value = .win := by
  apply win_of_move _ _ 33 (by decide) (by decide)
  have he : (⟨{4, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 4⟩ : Position).afterPick 33 = (⟨{4, 18, 35, 36, 52, 56, 62, 74, 100}, 29⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_168]
  rfl

private theorem node_170 : (⟨{33, 36, 52, 56, 62, 74, 100}, 31⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_171 : (⟨{33, 35, 36, 52, 56, 62, 74, 100}, 4⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{33, 35, 36, 52, 56, 62, 74, 100}, 4⟩ : Position).afterPick 35 = (⟨{33, 36, 52, 56, 62, 74, 100}, 31⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_170]
  rfl

private theorem node_172 : (⟨{7, 33, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 33, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 7 = (⟨{33, 35, 36, 52, 56, 62, 74, 100}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_171]
  rfl

private theorem node_173 : (⟨{4, 7, 33, 35, 36, 52, 56, 62, 74, 100}, 15⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 33, 35, 36, 52, 56, 62, 74, 100}, 15⟩ : Position).afterPick 4 = (⟨{7, 33, 35, 36, 52, 56, 62, 74, 100}, 11⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_172]
  rfl

private theorem node_174 : (⟨{7, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_175 : (⟨{7, 18, 36, 56, 62, 74, 100}, 43⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_176 : (⟨{7, 18, 36, 52, 62, 74, 100}, 47⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_177 : (⟨{7, 18, 36, 52, 56, 74, 100}, 53⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_178 : (⟨{7, 18, 36, 52, 56, 62, 100}, 65⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_179 : (⟨{7, 18, 36, 52, 56, 62, 74}, 91⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_180 : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 7 = (⟨{18, 36, 52, 56, 62, 74, 100}, 2⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_018]
    rfl
  · have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 18 = (⟨{7, 36, 52, 56, 62, 74, 100}, 9⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_174]
    rfl
  · have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 36 = (⟨{7, 18, 52, 56, 62, 74, 100}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_075]
    rfl
  · have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 52 = (⟨{7, 18, 36, 56, 62, 74, 100}, 43⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_175]
    rfl
  · have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 56 = (⟨{7, 18, 36, 52, 62, 74, 100}, 47⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_176]
    rfl
  · have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 62 = (⟨{7, 18, 36, 52, 56, 74, 100}, 53⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_177]
    rfl
  · have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 74 = (⟨{7, 18, 36, 52, 56, 62, 100}, 65⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_178]
    rfl
  · have he : (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position).afterPick 100 = (⟨{7, 18, 36, 52, 56, 62, 74}, 91⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_179]
    rfl

private theorem node_181 : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 26⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 26⟩ : Position).afterPick 35 = (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 9⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_180]
  rfl

private theorem node_182 : (⟨{4, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position).afterPick 4 = (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 26⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_181]
  rfl

private theorem node_183 : (⟨{7, 36, 52, 56, 62, 74, 100}, 13⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_184 : (⟨{4, 7, 36, 52, 56, 62, 74, 100}, 17⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 36, 52, 56, 62, 74, 100}, 17⟩ : Position).afterPick 4 = (⟨{7, 36, 52, 56, 62, 74, 100}, 13⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_183]
  rfl

private theorem node_185 : (⟨{4, 7, 18, 56, 62, 74, 100}, 17⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_186 : (⟨{4, 7, 18, 52, 56, 62, 74, 100}, 35⟩ : Position).value = .win := by
  apply win_of_move _ _ 52 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 52, 56, 62, 74, 100}, 35⟩ : Position).afterPick 52 = (⟨{4, 7, 18, 56, 62, 74, 100}, 17⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_185]
  rfl

private theorem node_187 : (⟨{4, 7, 36, 56, 62, 74, 100}, 33⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_188 : (⟨{4, 7, 18, 36, 56, 62, 74, 100}, 51⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 36, 56, 62, 74, 100}, 51⟩ : Position).afterPick 18 = (⟨{4, 7, 36, 56, 62, 74, 100}, 33⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_187]
  rfl

private theorem node_189 : (⟨{7, 18, 36, 52, 62, 74, 100}, 51⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_190 : (⟨{4, 7, 18, 36, 52, 62, 74, 100}, 55⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 36, 52, 62, 74, 100}, 55⟩ : Position).afterPick 4 = (⟨{7, 18, 36, 52, 62, 74, 100}, 51⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_189]
  rfl

private theorem node_191 : (⟨{7, 18, 36, 52, 56, 74, 100}, 57⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_192 : (⟨{4, 7, 18, 36, 52, 56, 74, 100}, 61⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 36, 52, 56, 74, 100}, 61⟩ : Position).afterPick 4 = (⟨{7, 18, 36, 52, 56, 74, 100}, 57⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_191]
  rfl

private theorem node_193 : (⟨{7, 18, 36, 52, 56, 62, 100}, 69⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_194 : (⟨{4, 7, 18, 36, 52, 56, 62, 100}, 73⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 36, 52, 56, 62, 100}, 73⟩ : Position).afterPick 4 = (⟨{7, 18, 36, 52, 56, 62, 100}, 69⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_193]
  rfl

private theorem node_195 : (⟨{7, 18, 36, 52, 56, 62, 74}, 95⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_196 : (⟨{4, 7, 18, 36, 52, 56, 62, 74}, 99⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74}, 99⟩ : Position).afterPick 4 = (⟨{7, 18, 36, 52, 56, 62, 74}, 95⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_195]
  rfl

private theorem node_197 : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 4 = (⟨{7, 18, 36, 52, 56, 62, 74, 100}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_131]
    rfl
  · have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 7 = (⟨{4, 18, 36, 52, 56, 62, 74, 100}, 6⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_155]
    rfl
  · have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 18 = (⟨{4, 7, 36, 52, 56, 62, 74, 100}, 17⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_184]
    rfl
  · have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 36 = (⟨{4, 7, 18, 52, 56, 62, 74, 100}, 35⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_186]
    rfl
  · have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 52 = (⟨{4, 7, 18, 36, 56, 62, 74, 100}, 51⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_188]
    rfl
  · have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 56 = (⟨{4, 7, 18, 36, 52, 62, 74, 100}, 55⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_190]
    rfl
  · have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 62 = (⟨{4, 7, 18, 36, 52, 56, 74, 100}, 61⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_192]
    rfl
  · have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 74 = (⟨{4, 7, 18, 36, 52, 56, 62, 100}, 73⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_194]
    rfl
  · have he : (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 100 = (⟨{4, 7, 18, 36, 52, 56, 62, 74}, 99⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_196]
    rfl

private theorem node_198 : (⟨{4, 7, 18, 33, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).value = .win := by
  apply win_of_move _ _ 33 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 33 = (⟨{4, 7, 18, 36, 52, 56, 62, 74, 100}, 1⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_197]
  rfl

private theorem node_199 : (⟨{18, 33, 35, 52, 56, 62, 74, 100}, 22⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 52, 56, 62, 74, 100}, 22⟩ : Position).afterPick 35 = (⟨{18, 33, 52, 56, 62, 74, 100}, 13⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_084]
  rfl

private theorem node_200 : (⟨{7, 18, 33, 35, 52, 56, 62, 74, 100}, 29⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 52, 56, 62, 74, 100}, 29⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 52, 56, 62, 74, 100}, 22⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_199]
  rfl

private theorem node_201 : (⟨{4, 7, 18, 33, 35, 52, 56, 62, 74, 100}, 33⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 52, 56, 62, 74, 100}, 33⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 52, 56, 62, 74, 100}, 29⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_200]
  rfl

private theorem node_202 : (⟨{7, 33, 35, 36, 62, 74, 100}, 29⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_203 : (⟨{7, 33, 35, 36, 56, 62, 74, 100}, 27⟩ : Position).value = .win := by
  apply win_of_move _ _ 56 (by decide) (by decide)
  have he : (⟨{7, 33, 35, 36, 56, 62, 74, 100}, 27⟩ : Position).afterPick 56 = (⟨{7, 33, 35, 36, 62, 74, 100}, 29⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_202]
  rfl

private theorem node_204 : (⟨{7, 18, 33, 35, 36, 56, 62, 74, 100}, 45⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 56, 62, 74, 100}, 45⟩ : Position).afterPick 18 = (⟨{7, 33, 35, 36, 56, 62, 74, 100}, 27⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_203]
  rfl

private theorem node_205 : (⟨{4, 7, 18, 33, 35, 36, 56, 62, 74, 100}, 49⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 56, 62, 74, 100}, 49⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 56, 62, 74, 100}, 45⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_204]
  rfl

private theorem node_206 : (⟨{33, 35, 36, 52, 62, 74, 100}, 24⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_207 : (⟨{18, 33, 35, 36, 52, 62, 74, 100}, 42⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 36, 52, 62, 74, 100}, 42⟩ : Position).afterPick 18 = (⟨{33, 35, 36, 52, 62, 74, 100}, 24⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_206]
  rfl

private theorem node_208 : (⟨{7, 18, 33, 35, 36, 52, 62, 74, 100}, 49⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 62, 74, 100}, 49⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 36, 52, 62, 74, 100}, 42⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_207]
  rfl

private theorem node_209 : (⟨{4, 7, 18, 33, 35, 36, 52, 62, 74, 100}, 53⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 52, 62, 74, 100}, 53⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 62, 74, 100}, 49⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_208]
  rfl

private theorem node_210 : (⟨{33, 35, 36, 52, 56, 74, 100}, 30⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_211 : (⟨{18, 33, 35, 36, 52, 56, 74, 100}, 48⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 36, 52, 56, 74, 100}, 48⟩ : Position).afterPick 18 = (⟨{33, 35, 36, 52, 56, 74, 100}, 30⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_210]
  rfl

private theorem node_212 : (⟨{7, 18, 33, 35, 36, 52, 56, 74, 100}, 55⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 56, 74, 100}, 55⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 36, 52, 56, 74, 100}, 48⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_211]
  rfl

private theorem node_213 : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 74, 100}, 59⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 74, 100}, 59⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 56, 74, 100}, 55⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_212]
  rfl

private theorem node_214 : (⟨{33, 35, 36, 52, 56, 62, 100}, 42⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_215 : (⟨{18, 33, 35, 36, 52, 56, 62, 100}, 60⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 36, 52, 56, 62, 100}, 60⟩ : Position).afterPick 18 = (⟨{33, 35, 36, 52, 56, 62, 100}, 42⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_214]
  rfl

private theorem node_216 : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 100}, 67⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 100}, 67⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 36, 52, 56, 62, 100}, 60⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_215]
  rfl

private theorem node_217 : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 100}, 71⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 100}, 71⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 56, 62, 100}, 67⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_216]
  rfl

private theorem node_218 : (⟨{33, 35, 36, 52, 56, 62, 74}, 68⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_219 : (⟨{18, 33, 35, 36, 52, 56, 62, 74}, 86⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{18, 33, 35, 36, 52, 56, 62, 74}, 86⟩ : Position).afterPick 18 = (⟨{33, 35, 36, 52, 56, 62, 74}, 68⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_218]
  rfl

private theorem node_220 : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74}, 93⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74}, 93⟩ : Position).afterPick 7 = (⟨{18, 33, 35, 36, 52, 56, 62, 74}, 86⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_219]
  rfl

private theorem node_221 : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74}, 97⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74}, 97⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74}, 93⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_220]
  rfl

private theorem node_222 : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 4 = (⟨{7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_145]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 7 = (⟨{4, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 4⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_169]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 18 = (⟨{4, 7, 33, 35, 36, 52, 56, 62, 74, 100}, 15⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_173]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 33 = (⟨{4, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_182]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 35 = (⟨{4, 7, 18, 33, 36, 52, 56, 62, 74, 100}, 32⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_198]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 36 = (⟨{4, 7, 18, 33, 35, 52, 56, 62, 74, 100}, 33⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_201]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 52 = (⟨{4, 7, 18, 33, 35, 36, 56, 62, 74, 100}, 49⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_205]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 56 = (⟨{4, 7, 18, 33, 35, 36, 52, 62, 74, 100}, 53⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_209]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 62 = (⟨{4, 7, 18, 33, 35, 36, 52, 56, 74, 100}, 59⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_213]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 74 = (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 100}, 71⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_217]
    rfl
  · have he : (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 100 = (⟨{4, 7, 18, 33, 35, 36, 52, 56, 62, 74}, 97⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_221]
    rfl

private theorem node_223 : (⟨{2, 36, 52, 56, 62, 74, 100}, 28⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_224 : (⟨{2, 35, 52, 56, 62, 74, 100}, 29⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_225 : (⟨{2, 35, 36, 56, 62, 74, 100}, 45⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_226 : (⟨{2, 35, 36, 52, 62, 74, 100}, 49⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_227 : (⟨{2, 35, 36, 52, 56, 74, 100}, 55⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_228 : (⟨{2, 35, 36, 52, 56, 62, 100}, 67⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_229 : (⟨{2, 35, 36, 52, 56, 62, 74}, 93⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_230 : (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).afterPick 2 = (⟨{35, 36, 52, 56, 62, 74, 100}, 5⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_001]
    rfl
  · have he : (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).afterPick 35 = (⟨{2, 36, 52, 56, 62, 74, 100}, 28⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_223]
    rfl
  · have he : (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).afterPick 36 = (⟨{2, 35, 52, 56, 62, 74, 100}, 29⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_224]
    rfl
  · have he : (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).afterPick 52 = (⟨{2, 35, 36, 56, 62, 74, 100}, 45⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_225]
    rfl
  · have he : (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).afterPick 56 = (⟨{2, 35, 36, 52, 62, 74, 100}, 49⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_226]
    rfl
  · have he : (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).afterPick 62 = (⟨{2, 35, 36, 52, 56, 74, 100}, 55⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_227]
    rfl
  · have he : (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).afterPick 74 = (⟨{2, 35, 36, 52, 56, 62, 100}, 67⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_228]
    rfl
  · have he : (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position).afterPick 100 = (⟨{2, 35, 36, 52, 56, 62, 74}, 93⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_229]
    rfl

private theorem node_231 : (⟨{18, 36, 52, 56, 62, 74, 100}, 8⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_232 : (⟨{2, 18, 36, 52, 56, 62, 74, 100}, 10⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 18, 36, 52, 56, 62, 74, 100}, 10⟩ : Position).afterPick 2 = (⟨{18, 36, 52, 56, 62, 74, 100}, 8⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_231]
  rfl

private theorem node_233 : (⟨{18, 35, 52, 56, 62, 74, 100}, 9⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_234 : (⟨{2, 18, 35, 52, 56, 62, 74, 100}, 11⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 18, 35, 52, 56, 62, 74, 100}, 11⟩ : Position).afterPick 2 = (⟨{18, 35, 52, 56, 62, 74, 100}, 9⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_233]
  rfl

private theorem node_235 : (⟨{18, 35, 36, 56, 62, 74, 100}, 25⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_236 : (⟨{2, 18, 35, 36, 56, 62, 74, 100}, 27⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 18, 35, 36, 56, 62, 74, 100}, 27⟩ : Position).afterPick 2 = (⟨{18, 35, 36, 56, 62, 74, 100}, 25⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_235]
  rfl

private theorem node_237 : (⟨{18, 35, 36, 52, 62, 74, 100}, 29⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_238 : (⟨{2, 18, 35, 36, 52, 62, 74, 100}, 31⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 18, 35, 36, 52, 62, 74, 100}, 31⟩ : Position).afterPick 2 = (⟨{18, 35, 36, 52, 62, 74, 100}, 29⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_237]
  rfl

private theorem node_239 : (⟨{18, 35, 36, 52, 56, 74, 100}, 35⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_240 : (⟨{2, 18, 35, 36, 52, 56, 74, 100}, 37⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 18, 35, 36, 52, 56, 74, 100}, 37⟩ : Position).afterPick 2 = (⟨{18, 35, 36, 52, 56, 74, 100}, 35⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_239]
  rfl

private theorem node_241 : (⟨{18, 35, 36, 52, 56, 62, 100}, 47⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_242 : (⟨{2, 18, 35, 36, 52, 56, 62, 100}, 49⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 18, 35, 36, 52, 56, 62, 100}, 49⟩ : Position).afterPick 2 = (⟨{18, 35, 36, 52, 56, 62, 100}, 47⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_241]
  rfl

private theorem node_243 : (⟨{18, 35, 36, 52, 56, 62, 74}, 73⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_244 : (⟨{2, 18, 35, 36, 52, 56, 62, 74}, 75⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74}, 75⟩ : Position).afterPick 2 = (⟨{18, 35, 36, 52, 56, 62, 74}, 73⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_243]
  rfl

private theorem node_245 : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 2 = (⟨{18, 35, 36, 52, 56, 62, 74, 100}, 23⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_009]
    rfl
  · have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 18 = (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_230]
    rfl
  · have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 35 = (⟨{2, 18, 36, 52, 56, 62, 74, 100}, 10⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_232]
    rfl
  · have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 36 = (⟨{2, 18, 35, 52, 56, 62, 74, 100}, 11⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_234]
    rfl
  · have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 52 = (⟨{2, 18, 35, 36, 56, 62, 74, 100}, 27⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_236]
    rfl
  · have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 56 = (⟨{2, 18, 35, 36, 52, 62, 74, 100}, 31⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_238]
    rfl
  · have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 62 = (⟨{2, 18, 35, 36, 52, 56, 74, 100}, 37⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_240]
    rfl
  · have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 74 = (⟨{2, 18, 35, 36, 52, 56, 62, 100}, 49⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_242]
    rfl
  · have he : (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position).afterPick 100 = (⟨{2, 18, 35, 36, 52, 56, 62, 74}, 75⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_244]
    rfl

private theorem node_246 : (⟨{7, 36, 52, 56, 62, 74, 100}, 19⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_247 : (⟨{2, 7, 36, 52, 56, 62, 74, 100}, 21⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 36, 52, 56, 62, 74, 100}, 21⟩ : Position).afterPick 2 = (⟨{7, 36, 52, 56, 62, 74, 100}, 19⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_246]
  rfl

private theorem node_248 : (⟨{7, 35, 52, 56, 62, 74, 100}, 20⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_249 : (⟨{2, 7, 35, 52, 56, 62, 74, 100}, 22⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 35, 52, 56, 62, 74, 100}, 22⟩ : Position).afterPick 2 = (⟨{7, 35, 52, 56, 62, 74, 100}, 20⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_248]
  rfl

private theorem node_250 : (⟨{7, 35, 36, 56, 62, 74, 100}, 36⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_251 : (⟨{2, 7, 35, 36, 56, 62, 74, 100}, 38⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 35, 36, 56, 62, 74, 100}, 38⟩ : Position).afterPick 2 = (⟨{7, 35, 36, 56, 62, 74, 100}, 36⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_250]
  rfl

private theorem node_252 : (⟨{7, 35, 36, 52, 62, 74, 100}, 40⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_253 : (⟨{2, 7, 35, 36, 52, 62, 74, 100}, 42⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 35, 36, 52, 62, 74, 100}, 42⟩ : Position).afterPick 2 = (⟨{7, 35, 36, 52, 62, 74, 100}, 40⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_252]
  rfl

private theorem node_254 : (⟨{7, 35, 36, 52, 56, 74, 100}, 46⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_255 : (⟨{2, 7, 35, 36, 52, 56, 74, 100}, 48⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 35, 36, 52, 56, 74, 100}, 48⟩ : Position).afterPick 2 = (⟨{7, 35, 36, 52, 56, 74, 100}, 46⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_254]
  rfl

private theorem node_256 : (⟨{7, 35, 36, 52, 56, 62, 100}, 58⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_257 : (⟨{2, 7, 35, 36, 52, 56, 62, 100}, 60⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 35, 36, 52, 56, 62, 100}, 60⟩ : Position).afterPick 2 = (⟨{7, 35, 36, 52, 56, 62, 100}, 58⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_256]
  rfl

private theorem node_258 : (⟨{7, 35, 36, 52, 56, 62, 74}, 84⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_259 : (⟨{2, 7, 35, 36, 52, 56, 62, 74}, 86⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74}, 86⟩ : Position).afterPick 2 = (⟨{7, 35, 36, 52, 56, 62, 74}, 84⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_258]
  rfl

private theorem node_260 : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 2 = (⟨{7, 35, 36, 52, 56, 62, 74, 100}, 12⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_017]
    rfl
  · have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 7 = (⟨{2, 35, 36, 52, 56, 62, 74, 100}, 7⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_230]
    rfl
  · have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 35 = (⟨{2, 7, 36, 52, 56, 62, 74, 100}, 21⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_247]
    rfl
  · have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 36 = (⟨{2, 7, 35, 52, 56, 62, 74, 100}, 22⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_249]
    rfl
  · have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 52 = (⟨{2, 7, 35, 36, 56, 62, 74, 100}, 38⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_251]
    rfl
  · have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 56 = (⟨{2, 7, 35, 36, 52, 62, 74, 100}, 42⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_253]
    rfl
  · have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 62 = (⟨{2, 7, 35, 36, 52, 56, 74, 100}, 48⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_255]
    rfl
  · have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 74 = (⟨{2, 7, 35, 36, 52, 56, 62, 100}, 60⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_257]
    rfl
  · have he : (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position).afterPick 100 = (⟨{2, 7, 35, 36, 52, 56, 62, 74}, 86⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_259]
    rfl

private theorem node_261 : (⟨{2, 18, 52, 56, 62, 74, 100}, 26⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_262 : (⟨{2, 7, 52, 56, 62, 74, 100}, 15⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_263 : (⟨{2, 7, 18, 56, 62, 74, 100}, 19⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_264 : (⟨{2, 7, 18, 52, 62, 74, 100}, 23⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_265 : (⟨{2, 7, 18, 52, 56, 74, 100}, 29⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_266 : (⟨{2, 7, 18, 52, 56, 62, 100}, 41⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_267 : (⟨{2, 7, 18, 52, 56, 62, 74}, 67⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_268 : (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).afterPick 2 = (⟨{7, 18, 52, 56, 62, 74, 100}, 31⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_132]
    rfl
  · have he : (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).afterPick 7 = (⟨{2, 18, 52, 56, 62, 74, 100}, 26⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_261]
    rfl
  · have he : (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).afterPick 18 = (⟨{2, 7, 52, 56, 62, 74, 100}, 15⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_262]
    rfl
  · have he : (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).afterPick 52 = (⟨{2, 7, 18, 56, 62, 74, 100}, 19⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_263]
    rfl
  · have he : (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).afterPick 56 = (⟨{2, 7, 18, 52, 62, 74, 100}, 23⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_264]
    rfl
  · have he : (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).afterPick 62 = (⟨{2, 7, 18, 52, 56, 74, 100}, 29⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_265]
    rfl
  · have he : (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).afterPick 74 = (⟨{2, 7, 18, 52, 56, 62, 100}, 41⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_266]
    rfl
  · have he : (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position).afterPick 100 = (⟨{2, 7, 18, 52, 56, 62, 74}, 67⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_267]
    rfl

private theorem node_269 : (⟨{2, 7, 18, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).value = .win := by
  apply win_of_move _ _ 36 (by decide) (by decide)
  have he : (⟨{2, 7, 18, 36, 52, 56, 62, 74, 100}, 3⟩ : Position).afterPick 36 = (⟨{2, 7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_268]
  rfl

private theorem node_270 : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 2⟩ : Position).value = .win := by
  apply win_of_move _ _ 35 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 2⟩ : Position).afterPick 35 = (⟨{7, 18, 52, 56, 62, 74, 100}, 33⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_130]
  rfl

private theorem node_271 : (⟨{2, 7, 18, 35, 52, 56, 62, 74, 100}, 4⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 18, 35, 52, 56, 62, 74, 100}, 4⟩ : Position).afterPick 2 = (⟨{7, 18, 35, 52, 56, 62, 74, 100}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_270]
  rfl

private theorem node_272 : (⟨{2, 7, 35, 36, 62, 74, 100}, 54⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_273 : (⟨{2, 7, 35, 36, 56, 62, 74, 100}, 2⟩ : Position).value = .win := by
  apply win_of_move _ _ 56 (by decide) (by decide)
  have he : (⟨{2, 7, 35, 36, 56, 62, 74, 100}, 2⟩ : Position).afterPick 56 = (⟨{2, 7, 35, 36, 62, 74, 100}, 54⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_272]
  rfl

private theorem node_274 : (⟨{2, 7, 18, 35, 36, 56, 62, 74, 100}, 20⟩ : Position).value = .win := by
  apply win_of_move _ _ 18 (by decide) (by decide)
  have he : (⟨{2, 7, 18, 35, 36, 56, 62, 74, 100}, 20⟩ : Position).afterPick 18 = (⟨{2, 7, 35, 36, 56, 62, 74, 100}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_273]
  rfl

private theorem node_275 : (⟨{18, 35, 36, 52, 62, 74, 100}, 15⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_276 : (⟨{7, 18, 35, 36, 52, 62, 74, 100}, 22⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 62, 74, 100}, 22⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 62, 74, 100}, 15⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_275]
  rfl

private theorem node_277 : (⟨{2, 7, 18, 35, 36, 52, 62, 74, 100}, 24⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 18, 35, 36, 52, 62, 74, 100}, 24⟩ : Position).afterPick 2 = (⟨{7, 18, 35, 36, 52, 62, 74, 100}, 22⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_276]
  rfl

private theorem node_278 : (⟨{18, 35, 36, 52, 56, 74, 100}, 21⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_279 : (⟨{7, 18, 35, 36, 52, 56, 74, 100}, 28⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 74, 100}, 28⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 56, 74, 100}, 21⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_278]
  rfl

private theorem node_280 : (⟨{2, 7, 18, 35, 36, 52, 56, 74, 100}, 30⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 18, 35, 36, 52, 56, 74, 100}, 30⟩ : Position).afterPick 2 = (⟨{7, 18, 35, 36, 52, 56, 74, 100}, 28⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_279]
  rfl

private theorem node_281 : (⟨{18, 35, 36, 52, 56, 62, 100}, 33⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_282 : (⟨{7, 18, 35, 36, 52, 56, 62, 100}, 40⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 62, 100}, 40⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 56, 62, 100}, 33⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_281]
  rfl

private theorem node_283 : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 100}, 42⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 100}, 42⟩ : Position).afterPick 2 = (⟨{7, 18, 35, 36, 52, 56, 62, 100}, 40⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_282]
  rfl

private theorem node_284 : (⟨{18, 35, 36, 52, 56, 62, 74}, 59⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_285 : (⟨{7, 18, 35, 36, 52, 56, 62, 74}, 66⟩ : Position).value = .win := by
  apply win_of_move _ _ 7 (by decide) (by decide)
  have he : (⟨{7, 18, 35, 36, 52, 56, 62, 74}, 66⟩ : Position).afterPick 7 = (⟨{18, 35, 36, 52, 56, 62, 74}, 59⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_284]
  rfl

private theorem node_286 : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74}, 68⟩ : Position).value = .win := by
  apply win_of_move _ _ 2 (by decide) (by decide)
  have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74}, 68⟩ : Position).afterPick 2 = (⟨{7, 18, 35, 36, 52, 56, 62, 74}, 66⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_285]
  rfl

private theorem node_287 : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 2 = (⟨{7, 18, 35, 36, 52, 56, 62, 74, 100}, 30⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_032]
    rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 7 = (⟨{2, 18, 35, 36, 52, 56, 62, 74, 100}, 25⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_245]
    rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 18 = (⟨{2, 7, 35, 36, 52, 56, 62, 74, 100}, 14⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_260]
    rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 35 = (⟨{2, 7, 18, 36, 52, 56, 62, 74, 100}, 3⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_269]
    rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 36 = (⟨{2, 7, 18, 35, 52, 56, 62, 74, 100}, 4⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_271]
    rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 52 = (⟨{2, 7, 18, 35, 36, 56, 62, 74, 100}, 20⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_274]
    rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 56 = (⟨{2, 7, 18, 35, 36, 52, 62, 74, 100}, 24⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_277]
    rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 62 = (⟨{2, 7, 18, 35, 36, 52, 56, 74, 100}, 30⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_280]
    rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 74 = (⟨{2, 7, 18, 35, 36, 52, 56, 62, 100}, 42⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_283]
    rfl
  · have he : (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position).afterPick 100 = (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74}, 68⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_286]
    rfl

private theorem node_288 : (⟨{2, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).value = .win := by
  apply win_of_move _ _ 33 (by decide) (by decide)
  have he : (⟨{2, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position).afterPick 33 = (⟨{2, 7, 18, 35, 36, 52, 56, 62, 74, 100}, 32⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_287]
  rfl

private theorem node_289 : (⟨{2, 4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 5⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{2, 4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 5⟩ : Position).afterPick 4 = (⟨{2, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 1⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_288]
  rfl

private theorem node_290 : (⟨{2, 3, 4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 8⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{2, 3, 4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 8⟩ : Position).afterPick 3 = (⟨{2, 4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100}, 5⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_289]
  rfl

def tail : Finset ℕ := {18, 33, 35, 36, 52, 56, 62, 74, 100}
def core : Finset ℕ := {4, 7} ∪ tail
def shadow : Finset ℕ := {2, 3, 4, 7} ∪ tail

/-- The witness has a positive even-sum tail, with every label above the anchors. -/
theorem arithmetic_premises :
    tail.card = 9 ∧ tail.sum id = 466 ∧ Even (tail.sum id) ∧
    (∀ x ∈ tail, 9 ≤ x) ∧ core.card = 11 ∧ core.sum id = 477 ∧
    shadow.card = 13 ∧ shadow.sum id = 482 := by
  decide +kernel

theorem core_one_loss : (⟨core, 1⟩ : Position).value = .loss := by
  have he : core = {4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100} := by decide
  simpa only [he] using node_112

theorem core_three_loss : (⟨core, 3⟩ : Position).value = .loss := by
  have he : core = {4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100} := by decide
  simpa only [he] using node_222

theorem shadow_eight_win : (⟨shadow, 8⟩ : Position).value = .win := by
  have he : shadow = {2, 3, 4, 7, 18, 33, 35, 36, 52, 56, 62, 74, 100} := by decide
  simpa only [he] using node_290

theorem every_pick_loses_at_one (x : ℕ) (hx : x ∈ core) :
    (⟨core, 1⟩ : Position).moveOutcome x = .loss := by
  exact (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mp
    core_one_loss x hx

theorem every_pick_loses_at_three (x : ℕ) (hx : x ∈ core) :
    (⟨core, 3⟩ : Position).moveOutcome x = .loss := by
  exact (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mp
    core_three_loss x hx

/-- Even tails above nine do not prohibit simultaneous losses at deficits one and three. -/
theorem not_uniform_two_anchor_separation :
    ¬ (∀ T : Finset ℕ, (∀ x ∈ T, 9 ≤ x) → Even (T.sum id) →
      (⟨{4, 7} ∪ T, 3⟩ : Position).value = .loss →
      (⟨{4, 7} ∪ T, 1⟩ : Position).value ≠ .loss) := by
  intro h
  obtain ⟨_, _, heven, hmin, _⟩ := arithmetic_premises
  exact h tail hmin heven core_three_loss core_one_loss

/-- The larger anchor-eight shadow wins, so this is not an anchor-B counterexample. -/
theorem shadow_eight_not_loss : (⟨shadow, 8⟩ : Position).value ≠ .loss := by
  rw [shadow_eight_win]
  decide

end CatchUp.TwoAnchorDoubleLossObstruction
