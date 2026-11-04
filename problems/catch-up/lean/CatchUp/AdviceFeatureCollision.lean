/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/AdviceFeatureCollision.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.WholeTurn
public import CatchUp.ExactSumLossObstruction

/-!
# A limitation of adjacent-pair arithmetic summaries

Two supports have the same pair count, selector interval, total, cardinality,
extrema, deficit, and effective parity. One wins and the other loses. These
are sparse normalized states, not counterexamples to the interval conjecture.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.AdviceFeatureCollision

open CatchUp (Position.move_outcome_eq_loss_of_value_eq_loss)

def leftStarts : Finset ℕ := {6, 10, 20, 40}
def rightStarts : Finset ℕ := {6, 12, 18, 40}

def least (S : Finset ℕ) : ℕ := if h : S.Nonempty then S.min' h else 0

def summary (B : Finset ℕ) : List ℕ :=
  [B.card, B.sum id, (SevenPairTest.pairedCounters B).card,
    (SevenPairTest.pairedCounters B).sum id,
    least (SevenPairTest.pairedCounters B), (SevenPairTest.pairedCounters B).sup id, 4]

theorem same_summary : summary leftStarts = summary rightStarts := by
  decide +kernel

def selectorSums (B : Finset ℕ) : Finset ℕ :=
  B.powerset.image (fun U ↦ (WholeTurn.preparation B U).sum id)

theorem same_selector_interval :
    selectorSums leftStarts = Finset.Icc 76 80 ∧
    selectorSums rightStarts = Finset.Icc 76 80 := by
  decide +kernel

theorem selector_sums (t : ℕ) (ht : t ≤ 4) :
    (∃ U ⊆ leftStarts, U.card = t ∧
      (WholeTurn.preparation leftStarts U).sum id = 76 + t) ∧
    (∃ U ⊆ rightStarts, U.card = t ∧
      (WholeTurn.preparation rightStarts U).sum id = 76 + t) := by
  constructor
  · obtain ⟨U, hU, hcard⟩ := Finset.exists_subset_card_eq
      (show t ≤ leftStarts.card by simpa [leftStarts] using ht)
    refine ⟨U, hU, hcard, ?_⟩
    simpa [leftStarts, hcard] using
      (WholeTurn.sum_preparation leftStarts U (by decide +kernel) hU)
  · obtain ⟨U, hU, hcard⟩ := Finset.exists_subset_card_eq
      (show t ≤ rightStarts.card by simpa [rightStarts] using ht)
    refine ⟨U, hU, hcard, ?_⟩
    simpa [rightStarts, hcard] using
      (WholeTurn.sum_preparation rightStarts U (by decide +kernel) hU)

theorem left_win :
    Position.value ⟨SevenPairTest.pairedCounters leftStarts, 4⟩ = .win := by
  have he : SevenPairTest.pairedCounters leftStarts =
      ({6, 7, 10, 11, 20, 21, 40, 41} : Finset ℕ) := by decide +kernel
  rw [he]
  exact (CanonicalFour.four_four_win_iff 6 10 20 40 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mpr
    ⟨rfl, rfl, rfl, rfl⟩

theorem right_loss :
    Position.value ⟨SevenPairTest.pairedCounters rightStarts, 4⟩ = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

theorem every_right_pick_loses (x : ℕ)
    (hx : x ∈ SevenPairTest.pairedCounters rightStarts) :
    (⟨SevenPairTest.pairedCounters rightStarts, 4⟩ : Position).moveOutcome x = .loss := by
  exact Position.move_outcome_eq_loss_of_value_eq_loss _ hx (by decide +kernel) right_loss

theorem opposite_outcomes_with_same_summary :
    summary leftStarts = summary rightStarts ∧
    Position.value ⟨SevenPairTest.pairedCounters leftStarts, 4⟩ = .win ∧
    Position.value ⟨SevenPairTest.pairedCounters rightStarts, 4⟩ = .loss :=
  ⟨same_summary, left_win, right_loss⟩

end CatchUp.AdviceFeatureCollision
