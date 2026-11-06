/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Classifier.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system.
-/
module

public import CatchUp.BoCowgill.Reference

/-!
# An executable classifier for one-sided safety

`check player position` is a Boolean recursion that follows `CanAvoidLoss`;
`check_eq_true_iff` proves them equivalent.
-/

@[expose] public section

namespace CatchUpSearch.CanAvoidLossClassifier

open CatchUp

/-- Executably decide whether a fixed player can avoid losing from a post-opening position. -/
def check (player : Player) (position : GamePosition) : Bool :=
  if position.IsTerminal then
    decide (position.terminalOutcomeFor player ≠ .loss)
  else if position.toMove = player then
    position.remaining.attach.fold (· || ·) false fun counter =>
      check player (position.afterPick counter.1)
  else
    position.remaining.attach.fold (· && ·) true fun counter =>
      check player (position.afterPick counter.1)
termination_by position.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    exact counter.2

/-- The executable classifier is exactly equivalent to proof-level one-sided non-loss. -/
theorem check_eq_true_iff (player : Player) (position : GamePosition) :
    check player position = true ↔ CanAvoidLoss player position := by
  rw [check.eq_def]
  by_cases hterminal : position.IsTerminal
  · simpa [hterminal] using
      (can_avoid_loss_iff_terminal_outcome_ne_loss player position hterminal).symm
  · by_cases htoMove : position.toMove = player
    · rw [ite_eq_right hterminal, ite_eq_left htoMove]
      rw [can_avoid_loss_iff_exists_safe_move player position hterminal htoMove]
      rw [Finset.fold_op_rel_iff_or (r := fun _ value : Bool => value = true) (c := true)
        (by simp)]
      simp only [Bool.false_eq_true, false_or, Finset.mem_attach]
      constructor
      · rintro ⟨⟨counter, hcounter⟩, _, hsafe⟩
        exact ⟨counter, hcounter, (check_eq_true_iff player _).1 hsafe⟩
      · rintro ⟨counter, hcounter, hsafe⟩
        exact ⟨⟨counter, hcounter⟩, True.intro, (check_eq_true_iff player _).2 hsafe⟩
    · rw [ite_eq_right hterminal, ite_eq_right htoMove]
      rw [can_avoid_loss_iff_forall_safe_moves player position hterminal htoMove]
      rw [Finset.fold_op_rel_iff_and (r := fun _ value : Bool => value = true) (c := true)
        (by simp)]
      simp only [true_and, Finset.mem_attach]
      constructor
      · intro hall counter hcounter
        exact (check_eq_true_iff player _).1 (hall ⟨counter, hcounter⟩ True.intro)
      · intro hall counter _
        have hcounter : position.LegalMove counter.1 := counter.2
        exact (check_eq_true_iff player _).2 (hall counter.1 hcounter)
termination_by position.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    assumption

end CatchUpSearch.CanAvoidLossClassifier
