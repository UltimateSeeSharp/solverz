/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/OddPairRootObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.DeficitTwo
public import CatchUp.WinningOpening

/-!
# An even number of odd-start adjacent pairs can have a winning root

This sparse six-pair support has a winning root with opening four.
The opponent LOSS child retains every legal reply. No uniqueness is claimed.
The proof DAG retains every losing-node choice and correct same-player continuations.
This is an obstruction to proposed induction lemmas, not to the interval conjecture.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.OddPairRootObstruction

open CatchUp (Position.value_eq_loss_iff_of_nonterminal)
open CatchUp.DeficitTwo (win_of_move)

private theorem node_001 : (⟨{66, 77, 78, 81, 82, 97, 98}, 63⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_002 : (⟨{65, 77, 78, 81, 82, 97, 98}, 64⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_003 : (⟨{65, 66, 78, 81, 82, 97, 98}, 75⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_004 : (⟨{65, 66, 77, 81, 82, 97, 98}, 76⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_005 : (⟨{65, 66, 77, 78, 82, 97, 98}, 79⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_006 : (⟨{65, 66, 77, 78, 81, 97, 98}, 80⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_007 : (⟨{65, 66, 77, 78, 81, 82, 98}, 95⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_008 : (⟨{65, 66, 77, 78, 81, 82, 97}, 96⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_009 : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 65 = (⟨{66, 77, 78, 81, 82, 97, 98}, 63⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_001]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 66 = (⟨{65, 77, 78, 81, 82, 97, 98}, 64⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_002]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 77 = (⟨{65, 66, 78, 81, 82, 97, 98}, 75⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_003]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 78 = (⟨{65, 66, 77, 81, 82, 97, 98}, 76⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_004]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 81 = (⟨{65, 66, 77, 78, 82, 97, 98}, 79⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_005]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 82 = (⟨{65, 66, 77, 78, 81, 97, 98}, 80⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_006]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 97 = (⟨{65, 66, 77, 78, 81, 82, 98}, 95⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_007]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 98 = (⟨{65, 66, 77, 78, 81, 82, 97}, 96⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_008]
    rfl

private theorem node_010 : (⟨{58, 65, 66, 77, 78, 81, 82, 97, 98}, 56⟩ : Position).value = .win := by
  apply win_of_move _ _ 58 (by decide) (by decide)
  have he : (⟨{58, 65, 66, 77, 78, 81, 82, 97, 98}, 56⟩ : Position).afterPick 58 = (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_009]
  rfl

private theorem node_011 : (⟨{65, 77, 78, 81, 82, 97, 98}, 48⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_012 : (⟨{57, 77, 78, 81, 82, 97, 98}, 56⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_013 : (⟨{57, 65, 78, 81, 82, 97, 98}, 68⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_014 : (⟨{57, 65, 77, 81, 82, 97, 98}, 69⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_015 : (⟨{57, 65, 77, 78, 82, 97, 98}, 72⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_016 : (⟨{57, 65, 77, 78, 81, 97, 98}, 73⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_017 : (⟨{57, 65, 77, 78, 81, 82, 98}, 88⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_018 : (⟨{57, 65, 77, 78, 81, 82, 97}, 89⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_019 : (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position).afterPick 57 = (⟨{65, 77, 78, 81, 82, 97, 98}, 48⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_011]
    rfl
  · have he : (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position).afterPick 65 = (⟨{57, 77, 78, 81, 82, 97, 98}, 56⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_012]
    rfl
  · have he : (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position).afterPick 77 = (⟨{57, 65, 78, 81, 82, 97, 98}, 68⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_013]
    rfl
  · have he : (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position).afterPick 78 = (⟨{57, 65, 77, 81, 82, 97, 98}, 69⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_014]
    rfl
  · have he : (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position).afterPick 81 = (⟨{57, 65, 77, 78, 82, 97, 98}, 72⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_015]
    rfl
  · have he : (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position).afterPick 82 = (⟨{57, 65, 77, 78, 81, 97, 98}, 73⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_016]
    rfl
  · have he : (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position).afterPick 97 = (⟨{57, 65, 77, 78, 81, 82, 98}, 88⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_017]
    rfl
  · have he : (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position).afterPick 98 = (⟨{57, 65, 77, 78, 81, 82, 97}, 89⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_018]
    rfl

private theorem node_020 : (⟨{57, 65, 66, 77, 78, 81, 82, 97, 98}, 57⟩ : Position).value = .win := by
  apply win_of_move _ _ 66 (by decide) (by decide)
  have he : (⟨{57, 65, 66, 77, 78, 81, 82, 97, 98}, 57⟩ : Position).afterPick 66 = (⟨{57, 65, 77, 78, 81, 82, 97, 98}, 9⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_019]
  rfl

private theorem node_021 : (⟨{58, 77, 78, 81, 82, 97, 98}, 55⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_022 : (⟨{57, 58, 78, 81, 82, 97, 98}, 75⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_023 : (⟨{57, 58, 77, 81, 82, 97, 98}, 76⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_024 : (⟨{57, 58, 77, 78, 82, 97, 98}, 79⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_025 : (⟨{57, 58, 77, 78, 81, 97, 98}, 80⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_026 : (⟨{57, 58, 77, 78, 81, 82, 98}, 95⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_027 : (⟨{57, 58, 77, 78, 81, 82, 97}, 96⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_028 : (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 57 = (⟨{58, 77, 78, 81, 82, 97, 98}, 55⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_021]
    rfl
  · have he : (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 58 = (⟨{57, 77, 78, 81, 82, 97, 98}, 56⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_012]
    rfl
  · have he : (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 77 = (⟨{57, 58, 78, 81, 82, 97, 98}, 75⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_022]
    rfl
  · have he : (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 78 = (⟨{57, 58, 77, 81, 82, 97, 98}, 76⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_023]
    rfl
  · have he : (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 81 = (⟨{57, 58, 77, 78, 82, 97, 98}, 79⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_024]
    rfl
  · have he : (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 82 = (⟨{57, 58, 77, 78, 81, 97, 98}, 80⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_025]
    rfl
  · have he : (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 97 = (⟨{57, 58, 77, 78, 81, 82, 98}, 95⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_026]
    rfl
  · have he : (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 98 = (⟨{57, 58, 77, 78, 81, 82, 97}, 96⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_027]
    rfl

private theorem node_029 : (⟨{57, 58, 66, 77, 78, 81, 82, 97, 98}, 64⟩ : Position).value = .win := by
  apply win_of_move _ _ 66 (by decide) (by decide)
  have he : (⟨{57, 58, 66, 77, 78, 81, 82, 97, 98}, 64⟩ : Position).afterPick 66 = (⟨{57, 58, 77, 78, 81, 82, 97, 98}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_028]
  rfl

private theorem node_030 : (⟨{58, 65, 77, 78, 81, 97, 98}, 40⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_031 : (⟨{57, 65, 77, 78, 81, 97, 98}, 41⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_032 : (⟨{57, 58, 77, 78, 81, 97, 98}, 48⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_033 : (⟨{57, 58, 65, 78, 81, 97, 98}, 60⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_034 : (⟨{57, 58, 65, 77, 81, 97, 98}, 61⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_035 : (⟨{57, 58, 65, 77, 78, 97, 98}, 64⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_036 : (⟨{57, 58, 65, 77, 78, 81, 98}, 80⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_037 : (⟨{57, 58, 65, 77, 78, 81, 97}, 81⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_038 : (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position).afterPick 57 = (⟨{58, 65, 77, 78, 81, 97, 98}, 40⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_030]
    rfl
  · have he : (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position).afterPick 58 = (⟨{57, 65, 77, 78, 81, 97, 98}, 41⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_031]
    rfl
  · have he : (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position).afterPick 65 = (⟨{57, 58, 77, 78, 81, 97, 98}, 48⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_032]
    rfl
  · have he : (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position).afterPick 77 = (⟨{57, 58, 65, 78, 81, 97, 98}, 60⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_033]
    rfl
  · have he : (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position).afterPick 78 = (⟨{57, 58, 65, 77, 81, 97, 98}, 61⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_034]
    rfl
  · have he : (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position).afterPick 81 = (⟨{57, 58, 65, 77, 78, 97, 98}, 64⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_035]
    rfl
  · have he : (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position).afterPick 97 = (⟨{57, 58, 65, 77, 78, 81, 98}, 80⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_036]
    rfl
  · have he : (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position).afterPick 98 = (⟨{57, 58, 65, 77, 78, 81, 97}, 81⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_037]
    rfl

private theorem node_039 : (⟨{57, 58, 65, 77, 78, 81, 82, 97, 98}, 65⟩ : Position).value = .win := by
  apply win_of_move _ _ 82 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 77, 78, 81, 82, 97, 98}, 65⟩ : Position).afterPick 82 = (⟨{57, 58, 65, 77, 78, 81, 97, 98}, 17⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_038]
  rfl

private theorem node_040 : (⟨{57, 58, 66, 78, 81, 97, 98}, 71⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_041 : (⟨{57, 58, 66, 78, 81, 82, 97, 98}, 11⟩ : Position).value = .win := by
  apply win_of_move _ _ 82 (by decide) (by decide)
  have he : (⟨{57, 58, 66, 78, 81, 82, 97, 98}, 11⟩ : Position).afterPick 82 = (⟨{57, 58, 66, 78, 81, 97, 98}, 71⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_040]
  rfl

private theorem node_042 : (⟨{57, 58, 65, 66, 78, 81, 82, 97, 98}, 76⟩ : Position).value = .win := by
  apply win_of_move _ _ 65 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 78, 81, 82, 97, 98}, 76⟩ : Position).afterPick 65 = (⟨{57, 58, 66, 78, 81, 82, 97, 98}, 11⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_041]
  rfl

private theorem node_043 : (⟨{57, 58, 65, 77, 81, 97, 98}, 71⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_044 : (⟨{57, 58, 65, 77, 81, 82, 97, 98}, 11⟩ : Position).value = .win := by
  apply win_of_move _ _ 82 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 77, 81, 82, 97, 98}, 11⟩ : Position).afterPick 82 = (⟨{57, 58, 65, 77, 81, 97, 98}, 71⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_043]
  rfl

private theorem node_045 : (⟨{57, 58, 65, 66, 77, 81, 82, 97, 98}, 77⟩ : Position).value = .win := by
  apply win_of_move _ _ 66 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 81, 82, 97, 98}, 77⟩ : Position).afterPick 66 = (⟨{57, 58, 65, 77, 81, 82, 97, 98}, 11⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_044]
  rfl

private theorem node_046 : (⟨{57, 58, 65, 77, 78, 97, 98}, 68⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_047 : (⟨{57, 58, 65, 77, 78, 82, 97, 98}, 14⟩ : Position).value = .win := by
  apply win_of_move _ _ 82 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 77, 78, 82, 97, 98}, 14⟩ : Position).afterPick 82 = (⟨{57, 58, 65, 77, 78, 97, 98}, 68⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_046]
  rfl

private theorem node_048 : (⟨{57, 58, 65, 66, 77, 78, 82, 97, 98}, 80⟩ : Position).value = .win := by
  apply win_of_move _ _ 66 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 78, 82, 97, 98}, 80⟩ : Position).afterPick 66 = (⟨{57, 58, 65, 77, 78, 82, 97, 98}, 14⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_047]
  rfl

private theorem node_049 : (⟨{58, 65, 66, 77, 78, 81, 97}, 40⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_050 : (⟨{57, 65, 66, 77, 78, 81, 97}, 41⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_051 : (⟨{57, 58, 66, 77, 78, 81, 97}, 48⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_052 : (⟨{57, 58, 65, 77, 78, 81, 97}, 49⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_053 : (⟨{57, 58, 65, 66, 78, 81, 97}, 60⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_054 : (⟨{57, 58, 65, 66, 77, 81, 97}, 61⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_055 : (⟨{57, 58, 65, 66, 77, 78, 97}, 64⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_056 : (⟨{57, 58, 65, 66, 77, 78, 81}, 80⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_057 : (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position).afterPick 57 = (⟨{58, 65, 66, 77, 78, 81, 97}, 40⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_049]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position).afterPick 58 = (⟨{57, 65, 66, 77, 78, 81, 97}, 41⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_050]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position).afterPick 65 = (⟨{57, 58, 66, 77, 78, 81, 97}, 48⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_051]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position).afterPick 66 = (⟨{57, 58, 65, 77, 78, 81, 97}, 49⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_052]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position).afterPick 77 = (⟨{57, 58, 65, 66, 78, 81, 97}, 60⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_053]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position).afterPick 78 = (⟨{57, 58, 65, 66, 77, 81, 97}, 61⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_054]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position).afterPick 81 = (⟨{57, 58, 65, 66, 77, 78, 97}, 64⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_055]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position).afterPick 97 = (⟨{57, 58, 65, 66, 77, 78, 81}, 80⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_056]
    rfl

private theorem node_058 : (⟨{57, 58, 65, 66, 77, 78, 81, 97, 98}, 81⟩ : Position).value = .win := by
  apply win_of_move _ _ 98 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97, 98}, 81⟩ : Position).afterPick 98 = (⟨{57, 58, 65, 66, 77, 78, 81, 97}, 17⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_057]
  rfl

private theorem node_059 : (⟨{57, 65, 77, 78, 81, 82, 98}, 28⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_060 : (⟨{57, 65, 66, 77, 78, 81, 82, 98}, 38⟩ : Position).value = .win := by
  apply win_of_move _ _ 66 (by decide) (by decide)
  have he : (⟨{57, 65, 66, 77, 78, 81, 82, 98}, 38⟩ : Position).afterPick 66 = (⟨{57, 65, 77, 78, 81, 82, 98}, 28⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_059]
  rfl

private theorem node_061 : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 98}, 96⟩ : Position).value = .win := by
  apply win_of_move _ _ 58 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 98}, 96⟩ : Position).afterPick 58 = (⟨{57, 65, 66, 77, 78, 81, 82, 98}, 38⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_060]
  rfl

private theorem node_062 : (⟨{57, 58, 77, 78, 81, 82, 97}, 34⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_063 : (⟨{57, 58, 66, 77, 78, 81, 82, 97}, 32⟩ : Position).value = .win := by
  apply win_of_move _ _ 66 (by decide) (by decide)
  have he : (⟨{57, 58, 66, 77, 78, 81, 82, 97}, 32⟩ : Position).afterPick 66 = (⟨{57, 58, 77, 78, 81, 82, 97}, 34⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_062]
  rfl

private theorem node_064 : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97}, 97⟩ : Position).value = .win := by
  apply win_of_move _ _ 65 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97}, 97⟩ : Position).afterPick 65 = (⟨{57, 58, 66, 77, 78, 81, 82, 97}, 32⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_063]
  rfl

private theorem node_065 : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 57 = (⟨{58, 65, 66, 77, 78, 81, 82, 97, 98}, 56⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_010]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 58 = (⟨{57, 65, 66, 77, 78, 81, 82, 97, 98}, 57⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_020]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 65 = (⟨{57, 58, 66, 77, 78, 81, 82, 97, 98}, 64⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_029]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 66 = (⟨{57, 58, 65, 77, 78, 81, 82, 97, 98}, 65⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_039]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 77 = (⟨{57, 58, 65, 66, 78, 81, 82, 97, 98}, 76⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_042]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 78 = (⟨{57, 58, 65, 66, 77, 81, 82, 97, 98}, 77⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_045]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 81 = (⟨{57, 58, 65, 66, 77, 78, 82, 97, 98}, 80⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_048]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 82 = (⟨{57, 58, 65, 66, 77, 78, 81, 97, 98}, 81⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_058]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 97 = (⟨{57, 58, 65, 66, 77, 78, 81, 82, 98}, 96⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_061]
    rfl
  · have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 98 = (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97}, 97⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_064]
    rfl

private theorem node_066 : (⟨{66, 77, 78, 81, 82, 97, 98}, 57⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_067 : (⟨{65, 77, 78, 81, 82, 97, 98}, 58⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_068 : (⟨{65, 66, 78, 81, 82, 97, 98}, 69⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_069 : (⟨{65, 66, 77, 81, 82, 97, 98}, 70⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_070 : (⟨{65, 66, 77, 78, 82, 97, 98}, 73⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_071 : (⟨{65, 66, 77, 78, 81, 97, 98}, 74⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_072 : (⟨{65, 66, 77, 78, 81, 82, 98}, 89⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_073 : (⟨{65, 66, 77, 78, 81, 82, 97}, 90⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_074 : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position).afterPick 65 = (⟨{66, 77, 78, 81, 82, 97, 98}, 57⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_066]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position).afterPick 66 = (⟨{65, 77, 78, 81, 82, 97, 98}, 58⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_067]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position).afterPick 77 = (⟨{65, 66, 78, 81, 82, 97, 98}, 69⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_068]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position).afterPick 78 = (⟨{65, 66, 77, 81, 82, 97, 98}, 70⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_069]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position).afterPick 81 = (⟨{65, 66, 77, 78, 82, 97, 98}, 73⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_070]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position).afterPick 82 = (⟨{65, 66, 77, 78, 81, 97, 98}, 74⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_071]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position).afterPick 97 = (⟨{65, 66, 77, 78, 81, 82, 98}, 89⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_072]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position).afterPick 98 = (⟨{65, 66, 77, 78, 81, 82, 97}, 90⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_073]
    rfl

private theorem node_075 : (⟨{58, 65, 66, 77, 78, 81, 82, 97, 98}, 50⟩ : Position).value = .win := by
  apply win_of_move _ _ 58 (by decide) (by decide)
  have he : (⟨{58, 65, 66, 77, 78, 81, 82, 97, 98}, 50⟩ : Position).afterPick 58 = (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 8⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_074]
  rfl

private theorem node_076 : (⟨{3, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 53⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 53⟩ : Position).afterPick 3 = (⟨{58, 65, 66, 77, 78, 81, 82, 97, 98}, 50⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_075]
  rfl

private theorem node_077 : (⟨{66, 77, 78, 81, 82, 97, 98}, 59⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_078 : (⟨{65, 77, 78, 81, 82, 97, 98}, 60⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_079 : (⟨{65, 66, 78, 81, 82, 97, 98}, 71⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_080 : (⟨{65, 66, 77, 81, 82, 97, 98}, 72⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_081 : (⟨{65, 66, 77, 78, 82, 97, 98}, 75⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_082 : (⟨{65, 66, 77, 78, 81, 97, 98}, 76⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_083 : (⟨{65, 66, 77, 78, 81, 82, 98}, 91⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_084 : (⟨{65, 66, 77, 78, 81, 82, 97}, 92⟩ : Position).value = .win := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_085 : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position).afterPick 65 = (⟨{66, 77, 78, 81, 82, 97, 98}, 59⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_077]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position).afterPick 66 = (⟨{65, 77, 78, 81, 82, 97, 98}, 60⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_078]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position).afterPick 77 = (⟨{65, 66, 78, 81, 82, 97, 98}, 71⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_079]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position).afterPick 78 = (⟨{65, 66, 77, 81, 82, 97, 98}, 72⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_080]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position).afterPick 81 = (⟨{65, 66, 77, 78, 82, 97, 98}, 75⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_081]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position).afterPick 82 = (⟨{65, 66, 77, 78, 81, 97, 98}, 76⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_082]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position).afterPick 97 = (⟨{65, 66, 77, 78, 81, 82, 98}, 91⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_083]
    rfl
  · have he : (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position).afterPick 98 = (⟨{65, 66, 77, 78, 81, 82, 97}, 92⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_084]
    rfl

private theorem node_086 : (⟨{57, 65, 66, 77, 78, 81, 82, 97, 98}, 51⟩ : Position).value = .win := by
  apply win_of_move _ _ 57 (by decide) (by decide)
  have he : (⟨{57, 65, 66, 77, 78, 81, 82, 97, 98}, 51⟩ : Position).afterPick 57 = (⟨{65, 66, 77, 78, 81, 82, 97, 98}, 6⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_085]
  rfl

private theorem node_087 : (⟨{3, 57, 65, 66, 77, 78, 81, 82, 97, 98}, 54⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 57, 65, 66, 77, 78, 81, 82, 97, 98}, 54⟩ : Position).afterPick 3 = (⟨{57, 65, 66, 77, 78, 81, 82, 97, 98}, 51⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_086]
  rfl

private theorem node_088 : (⟨{58, 77, 78, 81, 82, 97, 98}, 65⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_089 : (⟨{58, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).value = .win := by
  apply win_of_move _ _ 66 (by decide) (by decide)
  have he : (⟨{58, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position).afterPick 66 = (⟨{58, 77, 78, 81, 82, 97, 98}, 65⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_088]
  rfl

private theorem node_090 : (⟨{57, 58, 66, 77, 78, 81, 82, 97, 98}, 58⟩ : Position).value = .win := by
  apply win_of_move _ _ 57 (by decide) (by decide)
  have he : (⟨{57, 58, 66, 77, 78, 81, 82, 97, 98}, 58⟩ : Position).afterPick 57 = (⟨{58, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_089]
  rfl

private theorem node_091 : (⟨{3, 57, 58, 66, 77, 78, 81, 82, 97, 98}, 61⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 57, 58, 66, 77, 78, 81, 82, 97, 98}, 61⟩ : Position).afterPick 3 = (⟨{57, 58, 66, 77, 78, 81, 82, 97, 98}, 58⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_090]
  rfl

private theorem node_092 : (⟨{58, 77, 78, 81, 82, 97, 98}, 63⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_093 : (⟨{58, 65, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).value = .win := by
  apply win_of_move _ _ 65 (by decide) (by decide)
  have he : (⟨{58, 65, 77, 78, 81, 82, 97, 98}, 2⟩ : Position).afterPick 65 = (⟨{58, 77, 78, 81, 82, 97, 98}, 63⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_092]
  rfl

private theorem node_094 : (⟨{57, 58, 65, 77, 78, 81, 82, 97, 98}, 59⟩ : Position).value = .win := by
  apply win_of_move _ _ 57 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 77, 78, 81, 82, 97, 98}, 59⟩ : Position).afterPick 57 = (⟨{58, 65, 77, 78, 81, 82, 97, 98}, 2⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_093]
  rfl

private theorem node_095 : (⟨{3, 57, 58, 65, 77, 78, 81, 82, 97, 98}, 62⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 57, 58, 65, 77, 78, 81, 82, 97, 98}, 62⟩ : Position).afterPick 3 = (⟨{57, 58, 65, 77, 78, 81, 82, 97, 98}, 59⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_094]
  rfl

private theorem node_096 : (⟨{58, 65, 66, 81, 82, 97, 98}, 65⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_097 : (⟨{58, 65, 66, 78, 81, 82, 97, 98}, 13⟩ : Position).value = .win := by
  apply win_of_move _ _ 78 (by decide) (by decide)
  have he : (⟨{58, 65, 66, 78, 81, 82, 97, 98}, 13⟩ : Position).afterPick 78 = (⟨{58, 65, 66, 81, 82, 97, 98}, 65⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_096]
  rfl

private theorem node_098 : (⟨{57, 58, 65, 66, 78, 81, 82, 97, 98}, 70⟩ : Position).value = .win := by
  apply win_of_move _ _ 57 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 78, 81, 82, 97, 98}, 70⟩ : Position).afterPick 57 = (⟨{58, 65, 66, 78, 81, 82, 97, 98}, 13⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_097]
  rfl

private theorem node_099 : (⟨{3, 57, 58, 65, 66, 78, 81, 82, 97, 98}, 73⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 57, 58, 65, 66, 78, 81, 82, 97, 98}, 73⟩ : Position).afterPick 3 = (⟨{57, 58, 65, 66, 78, 81, 82, 97, 98}, 70⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_098]
  rfl

private theorem node_100 : (⟨{58, 65, 66, 81, 82, 97, 98}, 63⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_101 : (⟨{58, 65, 66, 77, 81, 82, 97, 98}, 14⟩ : Position).value = .win := by
  apply win_of_move _ _ 77 (by decide) (by decide)
  have he : (⟨{58, 65, 66, 77, 81, 82, 97, 98}, 14⟩ : Position).afterPick 77 = (⟨{58, 65, 66, 81, 82, 97, 98}, 63⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_100]
  rfl

private theorem node_102 : (⟨{57, 58, 65, 66, 77, 81, 82, 97, 98}, 71⟩ : Position).value = .win := by
  apply win_of_move _ _ 57 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 81, 82, 97, 98}, 71⟩ : Position).afterPick 57 = (⟨{58, 65, 66, 77, 81, 82, 97, 98}, 14⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_101]
  rfl

private theorem node_103 : (⟨{3, 57, 58, 65, 66, 77, 81, 82, 97, 98}, 74⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 57, 58, 65, 66, 77, 81, 82, 97, 98}, 74⟩ : Position).afterPick 3 = (⟨{57, 58, 65, 66, 77, 81, 82, 97, 98}, 71⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_102]
  rfl

private theorem node_104 : (⟨{57, 58, 66, 77, 78, 97, 98}, 73⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_105 : (⟨{57, 58, 66, 77, 78, 82, 97, 98}, 9⟩ : Position).value = .win := by
  apply win_of_move _ _ 82 (by decide) (by decide)
  have he : (⟨{57, 58, 66, 77, 78, 82, 97, 98}, 9⟩ : Position).afterPick 82 = (⟨{57, 58, 66, 77, 78, 97, 98}, 73⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_104]
  rfl

private theorem node_106 : (⟨{57, 58, 65, 66, 77, 78, 82, 97, 98}, 74⟩ : Position).value = .win := by
  apply win_of_move _ _ 65 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 78, 82, 97, 98}, 74⟩ : Position).afterPick 65 = (⟨{57, 58, 66, 77, 78, 82, 97, 98}, 9⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_105]
  rfl

private theorem node_107 : (⟨{3, 57, 58, 65, 66, 77, 78, 82, 97, 98}, 77⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 57, 58, 65, 66, 77, 78, 82, 97, 98}, 77⟩ : Position).afterPick 3 = (⟨{57, 58, 65, 66, 77, 78, 82, 97, 98}, 74⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_106]
  rfl

private theorem node_108 : (⟨{58, 65, 66, 77, 78, 97, 98}, 63⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_109 : (⟨{58, 65, 66, 77, 78, 81, 97, 98}, 18⟩ : Position).value = .win := by
  apply win_of_move _ _ 81 (by decide) (by decide)
  have he : (⟨{58, 65, 66, 77, 78, 81, 97, 98}, 18⟩ : Position).afterPick 81 = (⟨{58, 65, 66, 77, 78, 97, 98}, 63⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_108]
  rfl

private theorem node_110 : (⟨{57, 58, 65, 66, 77, 78, 81, 97, 98}, 75⟩ : Position).value = .win := by
  apply win_of_move _ _ 57 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 78, 81, 97, 98}, 75⟩ : Position).afterPick 57 = (⟨{58, 65, 66, 77, 78, 81, 97, 98}, 18⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_109]
  rfl

private theorem node_111 : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 97, 98}, 78⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 97, 98}, 78⟩ : Position).afterPick 3 = (⟨{57, 58, 65, 66, 77, 78, 81, 97, 98}, 75⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_110]
  rfl

private theorem node_112 : (⟨{58, 66, 77, 78, 81, 82, 98}, 32⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_113 : (⟨{58, 65, 66, 77, 78, 81, 82, 98}, 33⟩ : Position).value = .win := by
  apply win_of_move _ _ 65 (by decide) (by decide)
  have he : (⟨{58, 65, 66, 77, 78, 81, 82, 98}, 33⟩ : Position).afterPick 65 = (⟨{58, 66, 77, 78, 81, 82, 98}, 32⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_112]
  rfl

private theorem node_114 : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 98}, 90⟩ : Position).value = .win := by
  apply win_of_move _ _ 57 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 98}, 90⟩ : Position).afterPick 57 = (⟨{58, 65, 66, 77, 78, 81, 82, 98}, 33⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_113]
  rfl

private theorem node_115 : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 98}, 93⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 98}, 93⟩ : Position).afterPick 3 = (⟨{57, 58, 65, 66, 77, 78, 81, 82, 98}, 90⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_114]
  rfl

private theorem node_116 : (⟨{58, 66, 77, 78, 81, 82, 97}, 31⟩ : Position).value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

private theorem node_117 : (⟨{58, 65, 66, 77, 78, 81, 82, 97}, 34⟩ : Position).value = .win := by
  apply win_of_move _ _ 65 (by decide) (by decide)
  have he : (⟨{58, 65, 66, 77, 78, 81, 82, 97}, 34⟩ : Position).afterPick 65 = (⟨{58, 66, 77, 78, 81, 82, 97}, 31⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_116]
  rfl

private theorem node_118 : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97}, 91⟩ : Position).value = .win := by
  apply win_of_move _ _ 57 (by decide) (by decide)
  have he : (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97}, 91⟩ : Position).afterPick 57 = (⟨{58, 65, 66, 77, 78, 81, 82, 97}, 34⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_117]
  rfl

private theorem node_119 : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97}, 94⟩ : Position).value = .win := by
  apply win_of_move _ _ 3 (by decide) (by decide)
  have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97}, 94⟩ : Position).afterPick 3 = (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97}, 91⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_118]
  rfl

private theorem node_120 : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).value = .loss := by
  apply (Position.value_eq_loss_iff_of_nonterminal _ ⟨by decide, by decide⟩).mpr
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 3 = (⟨{57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 1⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_065]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 57 = (⟨{3, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 53⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_076]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 58 = (⟨{3, 57, 65, 66, 77, 78, 81, 82, 97, 98}, 54⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_087]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 65 = (⟨{3, 57, 58, 66, 77, 78, 81, 82, 97, 98}, 61⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_091]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 66 = (⟨{3, 57, 58, 65, 77, 78, 81, 82, 97, 98}, 62⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_095]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 77 = (⟨{3, 57, 58, 65, 66, 78, 81, 82, 97, 98}, 73⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_099]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 78 = (⟨{3, 57, 58, 65, 66, 77, 81, 82, 97, 98}, 74⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_103]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 81 = (⟨{3, 57, 58, 65, 66, 77, 78, 82, 97, 98}, 77⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_107]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 82 = (⟨{3, 57, 58, 65, 66, 77, 78, 81, 97, 98}, 78⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_111]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 97 = (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 98}, 93⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_115]
    rfl
  · have he : (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position).afterPick 98 = (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97}, 94⟩ : Position) := by decide
    rw [Position.moveOutcome, he, node_119]
    rfl

private theorem node_121 : (⟨{3, 4, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 0⟩ : Position).value = .win := by
  apply win_of_move _ _ 4 (by decide) (by decide)
  have he : (⟨{3, 4, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 0⟩ : Position).afterPick 4 = (⟨{3, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}, 4⟩ : Position) := by decide
  rw [Position.moveOutcome, he, node_120]
  rfl

def support : Finset ℕ := {3, 4, 57, 58, 65, 66, 77, 78, 81, 82, 97, 98}

theorem root_win : (⟨support, 0⟩ : Position).value = .win :=
  node_121

def starts : Finset ℕ := {3,57,65,77,81,97}

/-- The same certificate also contains this five-pair unit-deficit loss. -/
theorem five_pairs_one_loss :
    (⟨{57,58,65,66,77,78,81,82,97,98},1⟩ : Position).value = .loss :=
  node_065

theorem after_four_loss : (afterOpening support 4).value = .loss := by
  have he : afterOpening support 4 =
      (⟨{3,57,58,65,66,77,78,81,82,97,98},4⟩ : Position) := by decide
  rw [he, node_120]

theorem pair_geometry :
    starts.card = 6 ∧ Even starts.card ∧
      (∀ b ∈ starts, Odd b ∧ 3 ≤ b) ∧
      support = starts ∪ starts.image (fun b ↦ b + 1) ∧
      Disjoint starts (starts.image (fun b ↦ b + 1)) ∧
      (∀ b ∈ starts, ∀ c ∈ starts, b ≠ c →
        Disjoint ({b, b + 1} : Finset ℕ) {c, c + 1}) ∧
      support.card = 12 ∧ support.sum id = 766 ∧ Even (support.sum id) := by
  decide +kernel

theorem reference_win : value support = .win := by
  exact (initial_position_value_eq support).symm.trans root_win

theorem not_even_odd_pairs_nonwin :
    ¬ (∀ B : Finset ℕ, Even B.card → (∀ b ∈ B, Odd b ∧ 3 ≤ b) →
      (∀ b ∈ B, ∀ c ∈ B, b ≠ c →
        Disjoint ({b, b + 1} : Finset ℕ) {c, c + 1}) →
      value (B ∪ B.image (fun b ↦ b + 1)) ≠ .win) := by
  intro h
  have hs : starts ∪ starts.image (fun b ↦ b + 1) = support := by decide
  exact (show value support ≠ .win from
    hs ▸ h starts (by decide) (by decide) (by decide)) (reference_win)


end CatchUp.OddPairRootObstruction
