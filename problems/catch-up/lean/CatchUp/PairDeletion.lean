/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/PairDeletion.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Reference

/-!
# A Lower Pair-Deletion Reduction for Catch-Up

This module reduces the interval draw theorem to a one-parameter ray of normalized positions. If
every state obtained by deleting counters `1` and `b` is a non-loss for its player to move, and one
such state is a draw, then the original interval game is a draw.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

private theorem Position.value_ne_loss_of_move
    (position : Position) (x : ℕ)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬ position.remaining.sum (fun y => y) < position.deficit)
    (hx : x ∈ position.remaining)
    (hmove : position.moveOutcome x ≠ .loss) :
    position.value ≠ .loss := by
  rw [Position.value_eq_best_move_outcome position hremaining hcatch]
  rw [Outcome.best_ne_loss_iff]
  exact ⟨position.moveOutcome x, by
    apply List.mem_map.mpr
    exact ⟨⟨x, hx⟩, by simp, rfl⟩, hmove⟩

private theorem Position.value_ne_win_of_all_moves
    (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬ position.remaining.sum (fun y => y) < position.deficit)
    (hmoves : ∀ x ∈ position.remaining, position.moveOutcome x ≠ .win) :
    position.value ≠ .win := by
  rw [Position.value_eq_best_move_outcome position hremaining hcatch]
  rw [Outcome.best_ne_win_iff]
  intro outcome houtcome
  obtain ⟨⟨x, hx⟩, _, rfl⟩ := List.mem_map.mp houtcome
  exact hmoves x hx

/-- The normalized state after counters `a < b` have been taken from the interval game. -/
def pairDeletionPosition (N a b : ℕ) : Position :=
  ⟨((Finset.Icc 1 N).erase a).erase b, b - a⟩

/-- Every pair-deletion state on the ray from the minimum counter is a non-loss. -/
def LowerPairDeletionNonloss (N : ℕ) : Prop :=
  ∀ b ∈ Finset.Icc 1 N, 1 < b → (pairDeletionPosition N 1 b).value ≠ .loss

private theorem after_opening_one_value_ne_win_of_lower_pair_deletion_nonloss
    (N : ℕ) (hN : 2 ≤ N) (hpairs : LowerPairDeletionNonloss N) :
    (afterOpening (Finset.Icc 1 N) 1).value ≠ .win := by
  let position := afterOpening (Finset.Icc 1 N) 1
  have htwo : 2 ∈ position.remaining := by
    simp [position, afterOpening]
    omega
  have hremaining : position.remaining ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨2, htwo⟩
  have hsum : 2 ≤ position.remaining.sum (fun x => x) :=
    Finset.single_le_sum (fun x _ => Nat.zero_le x) htwo
  have hcatch : ¬position.remaining.sum (fun x => x) < position.deficit := by
    change ¬position.remaining.sum (fun x => x) < 1
    omega
  apply Position.value_ne_win_of_all_moves position hremaining hcatch
  intro b hb
  have hbIcc : b ∈ Finset.Icc 1 N := Finset.mem_of_mem_erase hb
  have hbNe : b ≠ 1 := Finset.ne_of_mem_erase hb
  have hbGt : 1 < b := by
    have := (Finset.mem_Icc.mp hbIcc).1
    omega
  have hp := hpairs b hbIcc hbGt
  simp only [position, Position.moveOutcome, afterOpening, Position.afterPick,
    not_lt_of_ge hbGt.le, ite_false]
  change (pairDeletionPosition N 1 b).value.neg ≠ .win
  intro hneg
  cases hvalue : (pairDeletionPosition N 1 b).value <;>
    simp [hvalue, Outcome.neg] at hneg hp

private theorem after_opening_value_ne_loss_of_lower_pair_deletion_nonloss
    (N : ℕ) (hN : 2 ≤ N) (hpairs : LowerPairDeletionNonloss N)
    (hpairDraw : (pairDeletionPosition N 1 2).value = .draw)
    (a : ℕ) (ha : a ∈ Finset.Icc 1 N) :
    (afterOpening (Finset.Icc 1 N) a).value ≠ .loss := by
  let position := afterOpening (Finset.Icc 1 N) a
  by_cases haOne : a = 1
  · subst a
    have htwo : 2 ∈ position.remaining := by
      simp [position, afterOpening]
      omega
    have hremaining : position.remaining ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp ⟨2, htwo⟩
    have hsum : 2 ≤ position.remaining.sum (fun x => x) :=
      Finset.single_le_sum (fun x _ => Nat.zero_le x) htwo
    have hcatch : ¬position.remaining.sum (fun x => x) < position.deficit := by
      change ¬position.remaining.sum (fun x => x) < 1
      omega
    apply Position.value_ne_loss_of_move position 2 hremaining hcatch htwo
    simp only [position, Position.moveOutcome, afterOpening, Position.afterPick,
      show ¬2 < 1 by omega, ite_false]
    change (pairDeletionPosition N 1 2).value.neg ≠ .loss
    simp [hpairDraw, Outcome.neg]
  · have haGt : 1 < a := by
      have := (Finset.mem_Icc.mp ha).1
      omega
    have hone : 1 ∈ position.remaining := by
      simp [position, afterOpening, ne_of_lt haGt]
      omega
    have hremaining : position.remaining ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp ⟨1, hone⟩
    have hsum : a ≤ position.remaining.sum (fun x => x) := by
      have hp := hpairs a ha haGt
      have hpairCatch :
          ¬(pairDeletionPosition N 1 a).remaining.sum (fun x => x) <
            (pairDeletionPosition N 1 a).deficit := by
        intro htooSmall
        have hpairLoss : (pairDeletionPosition N 1 a).value = .loss := by
          rw [Position.value.eq_def]
          by_cases hempty : (pairDeletionPosition N 1 a).remaining = ∅
          · have hdeficit : (pairDeletionPosition N 1 a).deficit ≠ 0 := by
              simp [pairDeletionPosition]
              omega
            simp [hempty, hdeficit]
          · simp [hempty, htooSmall]
        exact hp hpairLoss
      have hsumErase :
          (pairDeletionPosition N 1 a).remaining.sum (fun x => x) + 1 =
            position.remaining.sum (fun x => x) := by
        have hremainingEq :
            (pairDeletionPosition N 1 a).remaining = position.remaining.erase 1 := by
          ext x
          simp [pairDeletionPosition, position, afterOpening, and_left_comm, and_comm]
          omega
        rw [hremainingEq]
        exact Finset.sum_erase_add position.remaining (fun x => x) hone
      change ¬(pairDeletionPosition N 1 a).remaining.sum (fun x => x) < a - 1 at hpairCatch
      omega
    have hcatch : ¬position.remaining.sum (fun x => x) < position.deficit := by
      change ¬position.remaining.sum (fun x => x) < a
      omega
    apply Position.value_ne_loss_of_move position 1 hremaining hcatch hone
    have hafter : position.afterPick 1 = pairDeletionPosition N 1 a := by
      simp only [position, Position.afterPick, afterOpening, pairDeletionPosition, haGt, ite_true]
      congr 1
      ext x
      simp
      omega
    rw [Position.moveOutcome]
    simp only [show 1 < position.deficit by simpa [position, afterOpening] using haGt, ite_true]
    rw [hafter]
    exact hpairs a ha haGt

/-- Lower pair-deletion non-loss plus the first draw pair implies the interval game is a draw. -/
theorem value_Icc_eq_draw_of_lower_pair_deletion_nonloss
    (N : ℕ) (hN : 2 ≤ N)
    (hpairs : LowerPairDeletionNonloss N)
    (hpairDraw : (pairDeletionPosition N 1 2).value = .draw) :
    value (Finset.Icc 1 N) = .draw := by
  apply (value_eq_draw_iff_can_avoid_loss_after_opening (Finset.Icc 1 N)
    (Finset.nonempty_Icc.mpr (by omega))).2
  constructor
  · refine ⟨1, by simp; omega, ?_⟩
    rw [can_avoid_loss_iff_value]
    simpa using after_opening_one_value_ne_win_of_lower_pair_deletion_nonloss N hN hpairs
  · intro a ha
    rw [can_avoid_loss_iff_value]
    simpa using after_opening_value_ne_loss_of_lower_pair_deletion_nonloss
      N hN hpairs hpairDraw a ha

end CatchUp
