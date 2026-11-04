/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ExactSumLossObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates.
-/
module

public import Mathlib
public import CatchUp.WinningOpening
public import CatchUp.ZeroDeficit

/-!
# Exact-sum obstructions in losing Catch-Up positions

This module records a strategy-stealing obstruction for an exact-deficit block.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

theorem Position.move_outcome_eq_loss_of_value_eq_loss
    (position : Position) {x : ℕ}
    (hx : x ∈ position.remaining)
    (hcatch : ¬ position.remaining.sum (fun y => y) < position.deficit)
    (hloss : position.value = .loss) :
    position.moveOutcome x = .loss := by
  by_contra hmove
  have hremaining : position.remaining ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩
  have hbestNe :
      Outcome.best
          (position.remaining.attach.toList.map fun move =>
            position.moveOutcome move.1) ≠ .loss := by
    rw [Outcome.best_ne_loss_iff]
    refine ⟨position.moveOutcome x, ?_, hmove⟩
    apply List.mem_map.mpr
    exact ⟨⟨x, hx⟩, by simp, rfl⟩
  rw [Position.value_eq_best_move_outcome position hremaining hcatch] at hloss
  exact hbestNe hloss

theorem Position.loss_after_continuing_pick
    (position : Position) {x : ℕ}
    (hx : x ∈ position.remaining)
    (hcatch : ¬ position.remaining.sum (fun y => y) < position.deficit)
    (hxd : x < position.deficit)
    (hloss : position.value = .loss) :
    (position.afterPick x).value = .loss := by
  have hmove : position.moveOutcome x = .loss := by
    by_contra hmove
    have hremaining : position.remaining ≠ ∅ :=
      Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩
    have hbestNe :
        Outcome.best
            (position.remaining.attach.toList.map fun move =>
              position.moveOutcome move.1) ≠ .loss := by
      rw [Outcome.best_ne_loss_iff]
      refine ⟨position.moveOutcome x, ?_, hmove⟩
      apply List.mem_map.mpr
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
    rw [Position.value_eq_best_move_outcome position hremaining hcatch] at hloss
    exact hbestNe hloss
  simpa [Position.moveOutcome, hxd] using hmove

theorem Position.loss_after_erasing_subsum
    (remaining block : Finset ℕ) (deficit : ℕ)
    (hsub : block ⊆ remaining)
    (hlt : block.sum (fun x => x) < deficit)
    (hcatch : ¬ remaining.sum (fun x => x) < deficit)
    (hloss : (⟨remaining, deficit⟩ : Position).value = .loss) :
    (⟨remaining \ block, deficit - block.sum (fun x => x)⟩ : Position).value = .loss := by
  induction block using Finset.induction_on generalizing remaining deficit with
  | empty => simpa using hloss
  | @insert x block hxnot ih =>
      have hxRemaining : x ∈ remaining := hsub (by simp)
      have hsumInsert :
          (insert x block).sum (fun y => y) = block.sum (fun y => y) + x := by
        simp [hxnot, Nat.add_comm]
      have hxlt : x < deficit := by omega
      have hchildLoss :
          (⟨remaining.erase x, deficit - x⟩ : Position).value = .loss := by
        simpa [Position.afterPick, hxlt] using
          Position.loss_after_continuing_pick
            (⟨remaining, deficit⟩ : Position) hxRemaining hcatch hxlt hloss
      have hblockSub : block ⊆ remaining.erase x := by
        intro y hy
        apply Finset.mem_erase.mpr
        refine ⟨?_, hsub (by simp [hy])⟩
        intro hyx
        subst y
        exact hxnot hy
      have hblockLt : block.sum (fun y => y) < deficit - x := by omega
      have hsumErase :
          (remaining.erase x).sum (fun y => y) + x = remaining.sum (fun y => y) := by
        simpa using Finset.sum_erase_add remaining (fun y => y) hxRemaining
      have hchildCatch :
          ¬ (remaining.erase x).sum (fun y => y) < deficit - x := by omega
      have hih := ih (remaining.erase x) (deficit - x)
        hblockSub hblockLt hchildCatch hchildLoss
      have hremainingEq :
          remaining \ insert x block = remaining.erase x \ block := by
        ext y
        simp [and_assoc, and_left_comm, and_comm]
      have hdeficitEq :
          deficit - (insert x block).sum (fun y => y) =
            deficit - x - block.sum (fun y => y) := by omega
      rw [hremainingEq, hdeficitEq]
      exact hih

/-- If a losing position contains a positive exact-deficit block, then deleting that block gives
a tied winning game. Its unique winning opening is strictly larger than every member of the
deleted block. -/
theorem Position.exists_winning_opening_gt_max_of_loss_of_exact_sum
    (remaining block : Finset ℕ) (deficit : ℕ)
    (hblock : block.Nonempty)
    (hpositive : ∀ x ∈ block, 1 ≤ x)
    (hsub : block ⊆ remaining)
    (hsum : block.sum (fun x => x) = deficit)
    (hloss : (⟨remaining, deficit⟩ : Position).value = .loss) :
    ∃ w ∈ remaining \ block,
      (afterOpening (remaining \ block) w).value = .loss ∧ block.max' hblock < w := by
  have hcatch : ¬ remaining.sum (fun x => x) < deficit := by
    have hle := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
    change block.sum (fun x => x) ≤ remaining.sum (fun x => x) at hle
    rw [hsum] at hle
    omega
  let a := block.max' hblock
  have ha : a ∈ block := by simpa [a] using Finset.max'_mem block hblock
  have haPos : 1 ≤ a := hpositive a ha
  have hsumEraseA :
      (block.erase a).sum (fun x => x) + a = deficit := by
    rw [← hsum]
    simpa using Finset.sum_erase_add block (fun x => x) ha
  have hprefixSub : block.erase a ⊆ remaining :=
    (Finset.erase_subset a block).trans hsub
  have hprefixLt : (block.erase a).sum (fun x => x) < deficit := by omega
  have hprefixLoss := Position.loss_after_erasing_subsum remaining (block.erase a) deficit
    hprefixSub hprefixLt hcatch hloss
  have hdeficitPrefix : deficit - (block.erase a).sum (fun x => x) = a := by omega
  let prePosition : Position := ⟨remaining \ (block.erase a), a⟩
  have hpreLoss : prePosition.value = .loss := by
    simpa [prePosition, hdeficitPrefix] using hprefixLoss
  have haPre : a ∈ prePosition.remaining := by
    simp [prePosition, hsub ha]
  have hpreCatch :
      ¬ prePosition.remaining.sum (fun x => x) < prePosition.deficit := by
    have hle : a ≤ prePosition.remaining.sum (fun x => x) :=
      Finset.single_le_sum (fun x _ => Nat.zero_le x) haPre
    simpa [prePosition] using (show ¬prePosition.remaining.sum (fun x => x) < a by omega)
  have hmoveA : prePosition.moveOutcome a = .loss :=
    Position.move_outcome_eq_loss_of_value_eq_loss prePosition haPre hpreCatch hpreLoss
  have hremainingAfterA :
      (remaining \ (block.erase a)).erase a = remaining \ block := by
    rw [← Finset.insert_erase ha]
    ext y
    simp [and_left_comm]
    tauto
  have hresidualWin : CatchUp.value (remaining \ block) = .win := by
    simp only [Position.moveOutcome, prePosition, Position.afterPick,
      lt_self_iff_false, ite_false] at hmoveA
    simp only [Nat.sub_self] at hmoveA
    rw [hremainingAfterA, position_value_zero_deficit_eq_value] at hmoveA
    cases hvalue : CatchUp.value (remaining \ block) <;>
      simp [hvalue, Outcome.neg] at hmoveA ⊢
  have hresidualNonempty : (remaining \ block).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hresidualWin
    simp [CatchUp.value, valueAux.eq_def] at hresidualWin
  obtain ⟨w, hw, hwinW⟩ :=
    (value_eq_win_iff_exists_winning_opening
      (remaining \ block) hresidualNonempty).mp hresidualWin
  refine ⟨w, hw, hwinW, ?_⟩
  change a < w
  by_contra haw
  have hwNotBlock : w ∉ block := (Finset.mem_sdiff.mp hw).2
  have hwa : w < a := by
    have hne : w ≠ a := by
      intro hwa
      subst w
      exact hwNotBlock ha
    omega
  let exchangeBlock := insert w (block.erase a)
  have hwNotErase : w ∉ block.erase a := by simp [hwNotBlock]
  have hsumExchange :
      exchangeBlock.sum (fun x => x) = (block.erase a).sum (fun x => x) + w := by
    simp [exchangeBlock, hwNotErase, Nat.add_comm]
  have hexchangeSub : exchangeBlock ⊆ remaining := by
    intro x hx
    simp only [exchangeBlock, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact (Finset.mem_sdiff.mp hw).1
    · exact hsub (Finset.mem_of_mem_erase hx)
  have hexchangeLt : exchangeBlock.sum (fun x => x) < deficit := by omega
  have hexchangeLoss := Position.loss_after_erasing_subsum remaining exchangeBlock deficit
    hexchangeSub hexchangeLt hcatch hloss
  have hdeficitExchange : deficit - exchangeBlock.sum (fun x => x) = a - w := by omega
  let exchangePosition : Position := ⟨remaining \ exchangeBlock, a - w⟩
  have hexchangePositionLoss : exchangePosition.value = .loss := by
    simpa [exchangePosition, hdeficitExchange] using hexchangeLoss
  have haExchange : a ∈ exchangePosition.remaining := by
    simp [exchangePosition, exchangeBlock, hsub ha, ne_of_gt hwa]
  have hexchangeCatch :
      ¬ exchangePosition.remaining.sum (fun x => x) < exchangePosition.deficit := by
    have hle : a ≤ exchangePosition.remaining.sum (fun x => x) :=
      Finset.single_le_sum (fun x _ => Nat.zero_le x) haExchange
    change ¬ (remaining \ exchangeBlock).sum (fun x => x) < a - w
    change a ≤ (remaining \ exchangeBlock).sum (fun x => x) at hle
    omega
  have hmoveExchange : exchangePosition.moveOutcome a = .loss :=
    Position.move_outcome_eq_loss_of_value_eq_loss exchangePosition haExchange
      hexchangeCatch hexchangePositionLoss
  have hremainingExchangeAfterA :
      (remaining \ exchangeBlock).erase a = (remaining \ block).erase w := by
    rw [← Finset.insert_erase ha]
    ext y
    simp [exchangeBlock, and_left_comm]
    tauto
  have hafterExchangeA :
      exchangePosition.afterPick a = afterOpening (remaining \ block) w := by
    have hnotContinue : ¬a < a - w := by omega
    have hovershoot : a - (a - w) = w := by omega
    simp [exchangePosition, Position.afterPick, afterOpening,
      hremainingExchangeAfterA, hnotContinue, hovershoot]
  have hcatchA : ¬a < exchangePosition.deficit := by
    simp [exchangePosition]
  rw [Position.moveOutcome, ite_eq_right hcatchA, hafterExchangeA, hwinW] at hmoveExchange
  simp [Outcome.neg] at hmoveExchange

/-- A positive exact-deficit block whose maximum dominates the residual rules out a loss. -/
theorem Position.value_ne_loss_of_exact_sum_block_dominates
    (remaining block : Finset ℕ) (deficit : ℕ)
    (hblock : block.Nonempty)
    (hpositive : ∀ x ∈ block, 1 ≤ x)
    (hsub : block ⊆ remaining)
    (hsum : block.sum (fun x => x) = deficit)
    (hdominates : ∀ x ∈ remaining \ block, x ≤ block.max' hblock) :
    (⟨remaining, deficit⟩ : Position).value ≠ .loss := by
  intro hloss
  obtain ⟨w, hw, _, hgt⟩ :=
    Position.exists_winning_opening_gt_max_of_loss_of_exact_sum
      remaining block deficit hblock hpositive hsub hsum hloss
  exact (not_lt_of_ge (hdominates w hw)) hgt

end CatchUp
