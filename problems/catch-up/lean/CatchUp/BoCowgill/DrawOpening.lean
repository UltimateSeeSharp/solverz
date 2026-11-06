/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DrawOpening.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Reference

/-!
# Draw-valued openings in Catch-Up

This module proves that a nonempty Catch-Up game is drawn exactly when at least one opening leaves
a drawn normalized position. The reverse implication uses the two possible orders of two distinct
opening counters and includes the sparse terminal case.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- Picking two distinct opening counters in opposite orders negates the second-pick outcome. -/
theorem move_outcome_after_opening_comm (S : Finset ℕ) {p q : ℕ} (hpq : p ≠ q) :
    (afterOpening S p).moveOutcome q = ((afterOpening S q).moveOutcome p).neg := by
  have neg_neg (outcome : Outcome) : outcome.neg.neg = outcome := by
    cases outcome <;> rfl
  by_cases hqp : q < p
  · have hpnot : ¬ p < q := by omega
    simp [Position.moveOutcome, afterOpening, Position.afterPick, hqp, hpnot,
      Finset.erase_right_comm, Outcome.neg]
    exact (neg_neg _).symm
  · have hpqlt : p < q := by omega
    simp [Position.moveOutcome, afterOpening, Position.afterPick, hqp, hpqlt,
      Finset.erase_right_comm, Outcome.neg]

/-- If the available counters cannot close the deficit, every hypothetical pick is losing. -/
theorem Position.move_outcome_eq_loss_of_sum_lt_deficit (position : Position) {x : ℕ}
    (hx : x ∈ position.remaining)
    (hsum : position.remaining.sum (fun y ↦ y) < position.deficit) :
    position.moveOutcome x = .loss := by
  have hsum_erase : (position.remaining.erase x).sum (fun y ↦ y) + x =
      position.remaining.sum (fun y ↦ y) := by
    exact Finset.sum_erase_add position.remaining (fun y ↦ y) hx
  have hxlt : x < position.deficit := by omega
  have hchildsum : (position.remaining.erase x).sum (fun y ↦ y) <
      position.deficit - x := by
    omega
  simp only [Position.moveOutcome, Position.afterPick, hxlt, ite_true]
  rw [Position.value.eq_def]
  by_cases hempty : position.remaining.erase x = ∅
  · have hdeficit : position.deficit - x ≠ 0 := by omega
    simp [hempty, hdeficit]
  · simp [hempty, hchildsum]

/-- A nonempty Catch-Up game is drawn exactly when some opening has drawn post-opening value. -/
theorem value_eq_draw_iff_exists_draw_after_opening (S : Finset ℕ) (hS : S.Nonempty) :
    value S = .draw ↔ ∃ p ∈ S, (afterOpening S p).value = .draw := by
  rw [value_eq_best_after_opening S hS]
  constructor
  · intro hdraw
    have hparts := (Outcome.eq_draw_iff _).mp hdraw
    rw [Outcome.best_ne_loss_iff] at hparts
    obtain ⟨outcome, houtcome, hnotloss⟩ := hparts.1
    rw [Outcome.best_ne_win_iff] at hparts
    have hnotwin := hparts.2 outcome houtcome
    rcases List.mem_map.mp houtcome with ⟨⟨p, hp⟩, _, rfl⟩
    refine ⟨p, hp, ?_⟩
    cases hvalue : (afterOpening S p).value <;>
      simp [Outcome.neg, hvalue] at hnotloss hnotwin ⊢
  · rintro ⟨p, hp, hpdraw⟩
    rw [Outcome.eq_draw_iff]
    constructor
    · rw [Outcome.best_ne_loss_iff]
      refine ⟨(afterOpening S p).value.neg, ?_, ?_⟩
      · apply List.mem_map.mpr
        exact ⟨⟨p, hp⟩, by simp, rfl⟩
      · simp [hpdraw, Outcome.neg]
    · rw [Outcome.best_ne_win_iff]
      rintro outcome houtcome
      rcases List.mem_map.mp houtcome with ⟨⟨q, hq⟩, _, rfl⟩
      rw [Outcome.neg_ne_win_iff]
      by_cases hqp : q = p
      · subst q
        simp [hpdraw]
      · have hq_at_p : q ∈ (afterOpening S p).remaining := by
          simp [afterOpening, hq, hqp]
        have hpremaining : (afterOpening S p).remaining ≠ ∅ :=
          Finset.nonempty_iff_ne_empty.mp ⟨q, hq_at_p⟩
        have hpcatch : ¬ (afterOpening S p).remaining.sum (fun x ↦ x) <
            (afterOpening S p).deficit := by
          intro hlt
          have h := hpdraw
          rw [Position.value.eq_def] at h
          simp [hpremaining, hlt] at h
        have hpdraw' := hpdraw
        rw [Position.value_eq_best_move_outcome _ hpremaining hpcatch] at hpdraw'
        have hbestnw := ((Outcome.eq_draw_iff _).mp hpdraw').2
        rw [Outcome.best_ne_win_iff] at hbestnw
        have hmove_p : (afterOpening S p).moveOutcome q ≠ .win := by
          apply hbestnw
          apply List.mem_map.mpr
          exact ⟨⟨q, hq_at_p⟩, by simp, rfl⟩
        rw [move_outcome_after_opening_comm S (Ne.symm hqp),
          Outcome.neg_ne_win_iff] at hmove_p
        have hp_at_q : p ∈ (afterOpening S q).remaining := by
          exact Finset.mem_erase.mpr ⟨Ne.symm hqp, hp⟩
        have hqremaining : (afterOpening S q).remaining ≠ ∅ :=
          Finset.nonempty_iff_ne_empty.mp ⟨p, hp_at_q⟩
        have hqcatch : ¬ (afterOpening S q).remaining.sum (fun x ↦ x) <
            (afterOpening S q).deficit := by
          intro hlt
          exact hmove_p
            (Position.move_outcome_eq_loss_of_sum_lt_deficit _ hp_at_q hlt)
        rw [Position.value_eq_best_move_outcome _ hqremaining hqcatch,
          Outcome.best_ne_loss_iff]
        refine ⟨(afterOpening S q).moveOutcome p, ?_, hmove_p⟩
        apply List.mem_map.mpr
        exact ⟨⟨p, hp_at_q⟩, by simp, rfl⟩

end CatchUp
