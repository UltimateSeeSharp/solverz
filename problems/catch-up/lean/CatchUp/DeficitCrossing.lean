/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DeficitCrossing.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.PairEntranceShadow

/-!
# A legal midpoint turn excludes two losing deficits

The same chosen set continues at the higher deficit and completes a turn at the
lower one. Equal endpoint deficits would require both a loss and a win.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DeficitCrossing

/-- A losing high deficit excludes loss at a lower deficit when a legal turn
uses their midpoint mass. No density, parity, or cardinality bound is required. -/
theorem nonloss_of_loss_and_midpoint_turn (S Y : Finset ℕ) (d e final : ℕ)
    (hhigh : (⟨S, d⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨S, e⟩, .p1⟩ Y final)
    (hbelow : Y.sum (fun x ↦ x) < d)
    (hmid : d + e = 2 * Y.sum (fun x ↦ x)) :
    (⟨S, e⟩ : Position).value ≠ .loss := by
  intro hlow
  have hp := PairEntranceShadow.loss_after_subsum S Y d turn.chosen_subset hbelow hhigh
  have hw := PairEntranceShadow.turn_endpoint_win_of_loss ⟨S, e⟩ Y final turn hlow
  change (⟨S \ Y, Y.sum (fun x ↦ x) - e⟩ : Position).value = .win at hw
  have hdef : d - Y.sum (fun x ↦ x) = Y.sum (fun x ↦ x) - e := by omega
  rw [hdef, hw] at hp
  cases hp

/-- The legal turn `[2,3]` separates losing deficits seven and three on any support. -/
theorem seven_to_three (S : Finset ℕ) (h2 : 2 ∈ S) (h3 : 3 ∈ S)
    (hhigh : (⟨S, 7⟩ : Position).value = .loss) :
    (⟨S, 3⟩ : Position).value ≠ .loss := by
  apply nonloss_of_loss_and_midpoint_turn S {2, 3} 7 3 3 hhigh
  · refine ⟨by simp, ?_, by norm_num, Or.inr ?_⟩
    · simpa only [insert_subset_iff, singleton_subset_iff] using And.intro h2 h3
    · change (({2, 3} : Finset ℕ).erase 3).sum (fun x ↦ x) < 3
      decide +kernel
  all_goals norm_num

end CatchUp.DeficitCrossing
