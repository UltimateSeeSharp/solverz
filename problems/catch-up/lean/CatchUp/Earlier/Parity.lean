/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/Parity.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Reference

/-!
# Parity in Catch-Up

This module proves that a normalized Catch-Up position cannot be a draw when the sum of its
deficit and remaining counters is odd. It then transfers that invariant through the forced opening
move and shows that a player-one non-loss certificate at one opening of an odd-total game is a
strict win certificate.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

private theorem Outcome.best_ne_draw_of_forall (outcomes : List Outcome)
    (h : ∀ outcome ∈ outcomes, outcome ≠ .draw) :
    Outcome.best outcomes ≠ .draw := by
  intro hbest
  have hneLoss : Outcome.best outcomes ≠ .loss := by
    simp [hbest]
  have hneWin : Outcome.best outcomes ≠ .win := by
    simp [hbest]
  obtain ⟨outcome, houtcome, hnotLoss⟩ :=
    (Outcome.best_ne_loss_iff outcomes).mp hneLoss
  have hnotWin := (Outcome.best_ne_win_iff outcomes).mp hneWin outcome houtcome
  have hnotDraw := h outcome houtcome
  cases outcome <;> simp_all

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

@[simp]
private theorem Outcome.neg_ne_draw_iff (outcome : Outcome) :
    outcome.neg ≠ .draw ↔ outcome ≠ .draw := by
  cases outcome <;> simp [Outcome.neg]

private theorem odd_of_mod_eq_two {a b : ℕ} (hab : Nat.ModEq 2 a b) (hb : Odd b) : Odd a := by
  rw [Nat.odd_iff] at hb ⊢
  change a % 2 = b % 2 at hab
  exact hab.trans hb

/-- A legal pick preserves the parity of the deficit plus the remaining-counter sum. -/
theorem Position.mod_eq_two_deficit_add_sum_after_pick
    (position : Position) {x : ℕ} (hx : x ∈ position.remaining) :
    Nat.ModEq 2
      ((position.afterPick x).deficit +
        (position.afterPick x).remaining.sum (fun y => y))
      (position.deficit + position.remaining.sum (fun y => y)) := by
  have hsum :
      (position.remaining.erase x).sum (fun y => y) + x =
        position.remaining.sum (fun y => y) := by
    simpa using Finset.sum_erase_add position.remaining (fun y => y) hx
  by_cases hxd : x < position.deficit
  · simp only [Position.afterPick, hxd, ite_true]
    rw [Nat.ModEq]
    omega
  · have hdx : position.deficit ≤ x := by omega
    simp only [Position.afterPick, hxd, ite_false]
    rw [Nat.ModEq]
    omega

/-- If the deficit plus all remaining counters is odd, the position cannot have draw value. -/
theorem Position.value_ne_draw_of_odd (position : Position)
    (hodd : Odd (position.deficit + position.remaining.sum (fun x => x))) :
    position.value ≠ .draw := by
  rcases position with ⟨remaining, deficit⟩
  induction remaining using Finset.strongInduction generalizing deficit with
  | H remaining ih =>
      rw [Position.value.eq_def]
      by_cases hempty : remaining = ∅
      · subst remaining
        have hdeficit : deficit ≠ 0 := by
          intro hzero
          subst deficit
          simp at hodd
        simp [hdeficit]
      · simp only [hempty, ite_false]
        by_cases hlose : remaining.sum (fun x => x) < deficit
        · simp [hlose]
        · simp only [hlose, ite_false]
          apply Outcome.best_ne_draw_of_forall
          intro outcome houtcome
          obtain ⟨counter, _, rfl⟩ := List.mem_map.mp houtcome
          rcases counter with ⟨counter, hcounter⟩
          have hmod := Position.mod_eq_two_deficit_add_sum_after_pick
            ({ remaining := remaining, deficit := deficit } : Position) hcounter
          have hchildOdd := odd_of_mod_eq_two hmod hodd
          have hchild := ih (remaining.erase counter) (Finset.erase_ssubset hcounter)
            (({ remaining := remaining, deficit := deficit } : Position).afterPick counter).deficit
            hchildOdd
          by_cases hcontinue : counter < deficit
          · simpa only [hcontinue, ite_true, Position.afterPick] using hchild
          · simpa only [hcontinue, ite_false, Outcome.neg_ne_draw_iff, Position.afterPick] using hchild

/-- After a legal opening, deficit plus remaining sum is the original counter sum. -/
theorem deficit_add_sum_after_opening (S : Finset ℕ) {x : ℕ} (hx : x ∈ S) :
    (afterOpening S x).deficit +
        (afterOpening S x).remaining.sum (fun y => y) =
      S.sum (fun y => y) := by
  have hsum :
      (S.erase x).sum (fun y => y) + x = S.sum (fun y => y) := by
    simpa using Finset.sum_erase_add S (fun y => y) hx
  simp only [afterOpening]
  omega

/-- Every reachable interval position has the parity of the original interval sum. -/
theorem ReachableFromOpening.mod_eq_two_deficit_add_sum
    {N opening : ℕ} {position : GamePosition}
    (hreachable : ReachableFromOpening N opening position) :
    Nat.ModEq 2
      (position.deficit + position.remaining.sum (fun x => x))
      ((Finset.Icc 1 N).sum (fun x => x)) := by
  rcases hreachable with ⟨hopening, hsteps⟩
  induction hsteps with
  | refl =>
      have heq :
          (GamePosition.afterOpening (Finset.Icc 1 N) opening).deficit +
              (GamePosition.afterOpening (Finset.Icc 1 N) opening).remaining.sum (fun x => x) =
            (Finset.Icc 1 N).sum (fun x => x) := by
        simpa using deficit_add_sum_after_opening (Finset.Icc 1 N) hopening
      rw [heq]
  | tail hsteps hstep ih =>
      rcases hstep with ⟨_, x, hx, rfl⟩
      exact (Position.mod_eq_two_deficit_add_sum_after_pick _ hx).trans ih

/-- Every legal opening of an odd-total game gives a non-drawing normalized position. -/
theorem after_opening_value_ne_draw_of_odd_sum (S : Finset ℕ) {x : ℕ} (hx : x ∈ S)
    (hodd : Odd (S.sum (fun y => y))) :
    (afterOpening S x).value ≠ .draw := by
  apply Position.value_ne_draw_of_odd
  rw [deficit_add_sum_after_opening S hx]
  exact hodd

/-- A Catch-Up game with odd total counter sum cannot have draw value. -/
theorem value_ne_draw_of_odd_sum (S : Finset ℕ)
    (hodd : Odd (S.sum (fun y => y))) :
    value S ≠ .draw := by
  have hS : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    subst S
    simp at hodd
  rw [value_eq_best_after_opening S hS]
  apply Outcome.best_ne_draw_of_forall
  intro outcome houtcome
  obtain ⟨counter, _, rfl⟩ := List.mem_map.mp houtcome
  rcases counter with ⟨counter, hcounter⟩
  simpa only [Outcome.neg_ne_draw_iff] using
    after_opening_value_ne_draw_of_odd_sum S hcounter hodd

/-- In an odd-total game, a player-one non-loss certificate at one opening is a strict win. -/
theorem value_eq_win_of_odd_sum_and_can_avoid_loss_after_opening
    (S : Finset ℕ) {x : ℕ} (hx : x ∈ S)
    (hodd : Odd (S.sum (fun y => y)))
    (hsafe : CanAvoidLoss .p1 (GamePosition.afterOpening S x)) :
    value S = .win := by
  have hpostNotWin : (afterOpening S x).value ≠ .win := by
    have hvalue :=
      (can_avoid_loss_iff_value .p1 (GamePosition.afterOpening S x)).mp hsafe
    simpa using hvalue
  have hpostNotDraw := after_opening_value_ne_draw_of_odd_sum S hx hodd
  have hpostLoss : (afterOpening S x).value = .loss := by
    cases hvalue : (afterOpening S x).value <;> simp_all
  have hS : S.Nonempty := ⟨x, hx⟩
  rw [value_eq_best_after_opening S hS, Outcome.best_eq_win_iff]
  refine ⟨.win, ?_, rfl⟩
  apply List.mem_map.mpr
  refine ⟨⟨x, hx⟩, by simp, ?_⟩
  simp [hpostLoss, Outcome.neg]

end CatchUp
