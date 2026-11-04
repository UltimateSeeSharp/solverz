/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ReplyMaximumCompanion.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.ReplyDigraphReduction

/-!
# A conditional companion for a maximum opening's winning reply

The recovered statements require the pair-deletion positions below the maximum to
be nonempty and catchable. They do not assert unconditional outdegree exclusion.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- The position after opening with $c$ and then picking the smaller counter $a$. -/
def commonMaximumPairPosition (S : Finset ℕ) (a c : ℕ) : Position :=
  ⟨(S.erase a).erase c, c - a⟩

/-- The two-pick position is nonempty and its mover can still catch the deficit. -/
def CommonMaximumPairCatchable (S : Finset ℕ) (a c : ℕ) : Prop :=
  (commonMaximumPairPosition S a c).remaining ≠ ∅ ∧
    ¬ (commonMaximumPairPosition S a c).remaining.sum (fun x ↦ x) <
      (commonMaximumPairPosition S a c).deficit

private theorem Outcome.best_eq_win_iff (outcomes : List Outcome) :
    Outcome.best outcomes = .win ↔ ∃ outcome ∈ outcomes, outcome = .win := by
  classical
  simpa only [not_not, not_forall, Classical.not_imp, exists_prop] using
    (not_congr (Outcome.best_ne_win_iff outcomes))

private theorem Position.value_eq_win_of_winning_move (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit)
    (x : ℕ) (hx : x ∈ position.remaining) (hmove : position.moveOutcome x = .win) :
    position.value = .win := by
  rw [Position.value_eq_best_move_outcome position hremaining hcatch, Outcome.best_eq_win_iff]
  exact ⟨_, List.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩, hmove⟩

/-- A winning reply below a maximum has a distinct companion when all smaller
pair-deletion positions are nonempty and catchable. Both cross-picks are winning. -/
theorem reply_edge_from_max_has_companion (S : Finset ℕ) {a c : ℕ}
    (hmax : ∀ x ∈ S, x ≤ c)
    (hcatch : ∀ x ∈ S, x < c → CommonMaximumPairCatchable S x c)
    (hedge : ReplyEdge S c a) :
    ∃ b ∈ S, b ≠ a ∧ b < c ∧ ReplyEdge S c b ∧
      (commonMaximumPairPosition S a c).moveOutcome b = .win ∧
      (commonMaximumPairPosition S b c).moveOutcome a = .win := by
  rcases hedge with ⟨hc, ha, hca, hmove⟩
  have hac : a < c := lt_of_le_of_ne (hmax a ha) (Ne.symm hca)
  have hwin : (commonMaximumPairPosition S a c).value = .win := by
    simpa [afterOpening, Position.moveOutcome, Position.afterPick, hac,
      commonMaximumPairPosition, Finset.erase_right_comm] using hmove
  rw [Position.value_eq_best_move_outcome _ (hcatch a ha hac).1 (hcatch a ha hac).2,
    Outcome.best_eq_win_iff] at hwin
  obtain ⟨outcome, hmem, houtcome⟩ := hwin
  obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp hmem
  obtain ⟨hbc, hba, hbS⟩ : b ≠ c ∧ b ≠ a ∧ b ∈ S := by
    simpa [commonMaximumPairPosition] using hb
  have hblt : b < c := lt_of_le_of_ne (hmax b hbS) hbc
  have hcross : (commonMaximumPairPosition S a c).moveOutcome b =
      (commonMaximumPairPosition S b c).moveOutcome a := by
    rcases lt_or_gt_of_ne (Ne.symm hba) with hab | hab
    · exact pair_deletion_move_outcome_cross S hab hblt
    · exact (pair_deletion_move_outcome_cross S hab hac).symm
  have hcrosswin : (commonMaximumPairPosition S b c).moveOutcome a = .win :=
    hcross.symm.trans houtcome
  have habmem : a ∈ (commonMaximumPairPosition S b c).remaining := by
    simp [commonMaximumPairPosition, ha, Ne.symm hba, ne_of_lt hac]
  have hbwin : (commonMaximumPairPosition S b c).value = .win :=
    Position.value_eq_win_of_winning_move _ (hcatch b hbS hblt).1
      (hcatch b hbS hblt).2 a habmem hcrosswin
  refine ⟨b, hbS, hba, hblt, ⟨hc, hbS, Ne.symm hbc, ?_⟩, houtcome, hcrosswin⟩
  simpa [afterOpening, Position.moveOutcome, Position.afterPick, hblt,
    commonMaximumPairPosition, Finset.erase_right_comm] using hbwin

/-- Under the same catchability hypothesis, an outgoing reply edge at a maximum
cannot be the unique outgoing reply edge. -/
theorem reply_edge_from_max_not_unique (S : Finset ℕ) {a c : ℕ}
    (hmax : ∀ x ∈ S, x ≤ c)
    (hcatch : ∀ x ∈ S, x < c → CommonMaximumPairCatchable S x c)
    (hedge : ReplyEdge S c a) :
    ∃ b, b ≠ a ∧ ReplyEdge S c b := by
  obtain ⟨b, _, hba, _, hedgeB, _, _⟩ :=
    reply_edge_from_max_has_companion S hmax hcatch hedge
  exact ⟨b, hba, hedgeB⟩

end CatchUp
