/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/WinningOpening.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Reference

/-!
# Uniqueness of a Winning Catch-Up Opening

This module formalizes the crossing argument showing that a Catch-Up game on an arbitrary finite
set has at most one winning opening. It also characterizes a first-player win by the existence of
that unique opening.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

private theorem Outcome.best_eq_win_iff (outcomes : List Outcome) :
    Outcome.best outcomes = .win ↔ ∃ outcome ∈ outcomes, outcome = .win := by
  rw [← not_iff_not]
  simp
  constructor
  · intro hall hmem
    exact hall .win hmem rfl
  · intro hnot outcome hmem heq
    subst outcome
    exact hnot hmem

private theorem Outcome.best_eq_loss_iff (outcomes : List Outcome) :
    Outcome.best outcomes = .loss ↔ ∀ outcome ∈ outcomes, outcome = .loss := by
  rw [← not_iff_not]
  simp

theorem Position.value_eq_loss_iff_of_nonterminal (position : Position)
    (hnonterminal : position.remaining ≠ ∅ ∧
      ¬ position.remaining.sum (fun x => x) < position.deficit) :
    position.value = .loss ↔
      ∀ x ∈ position.remaining, position.moveOutcome x = .loss := by
  rw [Position.value_eq_best_move_outcome position hnonterminal.1 hnonterminal.2,
    Outcome.best_eq_loss_iff]
  simp [Position.moveOutcome]

@[simp]
private theorem Outcome.neg_eq_loss_iff (outcome : Outcome) :
    outcome.neg = .loss ↔ outcome = .win := by
  cases outcome <;> simp [Outcome.neg]

@[simp]
private theorem Outcome.neg_eq_win_iff (outcome : Outcome) :
    outcome.neg = .win ↔ outcome = .loss := by
  cases outcome <;> simp [Outcome.neg]

private theorem not_two_winning_openings_of_lt (S : Finset ℕ) {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
    (hwinA : (afterOpening S a).value = .loss)
    (hwinB : (afterOpening S b).value = .loss) : False := by
  let common : Position := ⟨(S.erase a).erase b, b - a⟩
  have hbRemaining : b ∈ (afterOpening S a).remaining := by
    simp [afterOpening, hb, ne_of_gt hab]
  have hremainingA : (afterOpening S a).remaining ≠ ∅ := by
    exact Finset.nonempty_iff_ne_empty.mp ⟨b, hbRemaining⟩
  have hsumB : b ≤ (afterOpening S a).remaining.sum (fun x ↦ x) := by
    exact Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hbRemaining
  have hcanCatchA :
      ¬ (afterOpening S a).remaining.sum (fun x ↦ x) < (afterOpening S a).deficit := by
    have hsumB' : b ≤ (S.erase a).sum (fun x ↦ x) := by
      simpa [afterOpening] using hsumB
    change ¬ (S.erase a).sum (fun x ↦ x) < a
    omega
  have hmoveA : (afterOpening S a).moveOutcome b = .loss :=
    (Position.value_eq_loss_iff_of_nonterminal (afterOpening S a)
      ⟨hremainingA, hcanCatchA⟩).mp hwinA b hbRemaining
  have hcommonWin : common.value = .win := by
    simp only [Position.moveOutcome, afterOpening, Position.afterPick,
      not_lt_of_ge hab.le, ite_false] at hmoveA
    change common.value.neg = .loss at hmoveA
    exact (Outcome.neg_eq_loss_iff common.value).mp hmoveA
  have haRemaining : a ∈ (afterOpening S b).remaining := by
    simp [afterOpening, ha, ne_of_lt hab]
  by_cases hsparse :
      (afterOpening S b).remaining.sum (fun x ↦ x) < (afterOpening S b).deficit
  · have hsparse' : (S.erase b).sum (fun x ↦ x) < b := by
      simpa [afterOpening] using hsparse
    have hsumErase :
        ((S.erase b).erase a).sum (fun x ↦ x) + a =
          (S.erase b).sum (fun x ↦ x) := by
      simpa [afterOpening] using
        (Finset.sum_erase_add (S.erase b) (fun x ↦ x) haRemaining)
    have hcommonSparse : common.remaining.sum (fun x ↦ x) < common.deficit := by
      dsimp [common]
      rw [Finset.erase_right_comm]
      omega
    have hcommonLoss : common.value = .loss := by
      rw [Position.value.eq_def]
      by_cases hempty : common.remaining = ∅
      · have hdeficit : common.deficit ≠ 0 := by
          intro hzero
          simp [hempty, hzero] at hcommonSparse
        simp [hempty, hdeficit]
      · simp [hempty, hcommonSparse]
    rw [hcommonWin] at hcommonLoss
    cases hcommonLoss
  · have hremainingB : (afterOpening S b).remaining ≠ ∅ := by
      exact Finset.nonempty_iff_ne_empty.mp ⟨a, haRemaining⟩
    have hmoveB : (afterOpening S b).moveOutcome a = .loss :=
      (Position.value_eq_loss_iff_of_nonterminal (afterOpening S b)
        ⟨hremainingB, hsparse⟩).mp hwinB a haRemaining
    have hcommonLoss : common.value = .loss := by
      simp only [Position.moveOutcome, afterOpening, Position.afterPick, hab, ite_true] at hmoveB
      simpa [common, Finset.erase_right_comm] using hmoveB
    rw [hcommonWin] at hcommonLoss
    cases hcommonLoss

/-- A Catch-Up game on an arbitrary finite set has at most one winning opening. -/
theorem winning_opening_unique (S : Finset ℕ) {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S)
    (hwinA : (afterOpening S a).value = .loss)
    (hwinB : (afterOpening S b).value = .loss) :
    a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (not_two_winning_openings_of_lt S ha hb hab hwinA hwinB).elim
  · exact hab
  · exact (not_two_winning_openings_of_lt S hb ha hab hwinB hwinA).elim

/-- A nonempty Catch-Up game is a first-player win exactly when some opening is winning. -/
theorem value_eq_win_iff_exists_winning_opening (S : Finset ℕ) (hS : S.Nonempty) :
    value S = .win ↔ ∃ x ∈ S, (afterOpening S x).value = .loss := by
  rw [value_eq_best_after_opening S hS, Outcome.best_eq_win_iff]
  simp

/-- A nonempty Catch-Up game is a first-player win exactly when it has a unique winning opening. -/
theorem value_eq_win_iff_exists_unique_winning_opening (S : Finset ℕ) (hS : S.Nonempty) :
    value S = .win ↔ ∃! x, x ∈ S ∧ (afterOpening S x).value = .loss := by
  rw [value_eq_win_iff_exists_winning_opening S hS]
  constructor
  · rintro ⟨x, hx, hwin⟩
    refine ⟨x, ⟨hx, hwin⟩, ?_⟩
    intro y hy
    exact winning_opening_unique S hy.1 hx hy.2 hwin
  · rintro ⟨x, hx, _⟩
    exact ⟨x, hx.1, hx.2⟩

/-- An interval game is a first-player win exactly when it has a unique winning opening. -/
theorem value_Icc_eq_win_iff_exists_unique_winning_opening (N : ℕ) (hN : 1 ≤ N) :
    value (Finset.Icc 1 N) = .win ↔
      ∃! x, x ∈ Finset.Icc 1 N ∧
        (afterOpening (Finset.Icc 1 N) x).value = .loss := by
  exact value_eq_win_iff_exists_unique_winning_opening
    (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)

end CatchUp
