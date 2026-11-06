/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/IntervalSuccessorReplyObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Executable
public import CatchUp.BoCowgill.CompletedTurn

/-!
# The immediate-successor reply can lose at an actual drawn interval endpoint

This finite diagnostic is reached by core pick four and opponent pick eleven
at N=15. It certifies the endpoint and every first pick, without evaluating
the full core root or asserting a counterexample to the interval conjecture.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.IntervalSuccessorReplyObstruction

/-- The actual endpoint after opponent pick eleven. -/
def endpoint : Position := ⟨{7, 9, 10, 12, 13, 14, 15}, 8⟩

/-- The opponent position after the proposed immediate-successor reply twelve. -/
def afterTwelve : Position := ⟨{7, 9, 10, 13, 14, 15}, 4⟩

/-- The actual interval-family core, with its original mover identified. -/
def coreGame : GamePosition := ⟨⟨{4, 7} ∪ Icc 9 15, 1⟩, .p1⟩

/-- Shared exact child values, each accounting for every subsequent opponent play. -/
theorem child_values :
    (endpoint.afterPick 7).value = .draw ∧
    (endpoint.afterPick 9).value = .draw ∧
    (endpoint.afterPick 10).value = .draw ∧
    (endpoint.afterPick 12).value = .win ∧
    (endpoint.afterPick 13).value = .draw ∧
    (endpoint.afterPick 14).value = .win ∧
    (endpoint.afterPick 15).value = .draw := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [← Position.eval_eq_value]
  all_goals decide +kernel

/-- The complete seven-counter first-pick map, shared from the child certificates. -/
theorem first_pick_values :
    endpoint.moveOutcome 7 = .draw ∧ endpoint.moveOutcome 9 = .draw ∧
    endpoint.moveOutcome 10 = .draw ∧ endpoint.moveOutcome 12 = .loss ∧
    endpoint.moveOutcome 13 = .draw ∧ endpoint.moveOutcome 14 = .loss ∧
    endpoint.moveOutcome 15 = .draw := by
  obtain ⟨h7, h9, h10, h12, h13, h14, h15⟩ := child_values
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num only [Position.moveOutcome, endpoint]
  all_goals simp_all only [endpoint, Outcome.neg, ite_true, ite_false]

/-- The actual endpoint is drawn, derived from its shared first-pick map. -/
theorem endpoint_draw : endpoint.value = .draw := by
  obtain ⟨h7, h9, h10, h12, h13, h14, h15⟩ := first_pick_values
  rw [Position.value_eq_best_move_outcome endpoint (by decide +kernel) (by decide +kernel),
    Outcome.eq_draw_iff, Outcome.best_ne_loss_iff, Outcome.best_ne_win_iff]
  constructor
  · refine ⟨endpoint.moveOutcome 7,
      List.mem_map.mpr ⟨⟨7, by decide +kernel⟩, by simp, rfl⟩, ?_⟩
    simp [h7]
  · intro outcome houtcome
    rcases List.mem_map.mp houtcome with ⟨⟨x, hx⟩, _, rfl⟩
    have hc : x = 7 ∨ x = 9 ∨ x = 10 ∨ x = 12 ∨ x = 13 ∨ x = 14 ∨ x = 15 := by
      simpa [endpoint] using hx
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [h7, h9, h10, h12, h13, h14, h15]

/-- Literal agreement with the reserve endpoint at N=15 and erased counter eleven. -/
theorem endpoint_support_identity :
    (⟨(insert 7 (Icc 9 15)).erase 11, 11 - 3⟩ : Position) = endpoint := by
  decide +kernel

/-- The proposed reply twelve leaves the advertised six-counter opponent position. -/
theorem after_twelve_identity : endpoint.afterPick 12 = afterTwelve := by
  decide +kernel

/-- The opponent can force a strict win after the proposed reply twelve. -/
theorem after_twelve_win : afterTwelve.value = .win := by
  simpa only [after_twelve_identity] using child_values.2.2.2.1

/-- The immediate-successor first pick twelve loses even though the endpoint is drawn. -/
theorem successor_reply_loses : endpoint.value = .draw ∧ endpoint.moveOutcome 12 = .loss :=
  ⟨endpoint_draw, first_pick_values.2.2.2.1⟩

/-- Four then opponent eleven returns the move to the original core mover. -/
theorem core_context :
    (coreGame.afterPick 4).afterPick 11 = (⟨endpoint, .p1⟩ : GamePosition) := by
  decide +kernel

/-- Both picks in the displayed core context are legal steps from nonterminal states. -/
theorem core_context_steps :
    coreGame.Step (coreGame.afterPick 4) ∧
      (coreGame.afterPick 4).Step (⟨endpoint, .p1⟩ : GamePosition) := by
  constructor
  · exact GamePosition.step_after_pick coreGame 4 (by decide +kernel)
      (by change 4 ∈ coreGame.remaining; decide +kernel)
  · have hp := GamePosition.step_after_pick (coreGame.afterPick 4) 11
      (by decide +kernel) (by change 11 ∈ (coreGame.afterPick 4).remaining; decide +kernel)
    simpa only [core_context] using hp

end CatchUp.IntervalSuccessorReplyObstruction
