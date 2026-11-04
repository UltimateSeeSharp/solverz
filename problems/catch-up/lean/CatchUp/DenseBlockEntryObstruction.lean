/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseBlockEntryObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Executable
public import CatchUp.CompletedTurn
public import CatchUp.ExactSumLossObstruction

/-!
# A dense obstruction to mandatory entry through an exact block

This finite diagnostic satisfies the dense subsum-gap branch hypotheses, but neither member
of its maximal exact block is a safe first pick in the continuing state. The continuing state
is drawn, with a unique safe first pick. All values below use the executable/value bridge.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseBlockEntryObstruction

open CatchUp (Position.loss_after_continuing_pick)

/-- The dense parent support. -/
def support : Finset ℕ := {4, 5, 6, 7, 8, 10, 11}

/-- The unique exact-nine block. -/
def block : Finset ℕ := {4, 5}

/-- The parent position; pick six continues to `low`. -/
def parent : Position := ⟨support, 9⟩

/-- The residual opening after removing the exact block. -/
def residual : Position := ⟨(support \ block).erase 6, 6⟩

/-- The subsum-gap continuing position. -/
def low : Position := ⟨support.erase 6, 3⟩

/-- The state after the sole safe first pick, viewed from the original player's perspective. -/
def afterEight : GamePosition := (⟨low, .p1⟩ : GamePosition).afterPick 8

/-- All scalar, support, parity, exact-block, and nonterminal branch premises. -/
theorem arithmetic_premises :
    support ⊆ Icc 1 11 ∧ Icc 1 11 \ support = {1, 2, 3, 9} ∧
    (Icc 1 11 \ support).card = 4 ∧
    2 * (Icc 1 11 \ support).card + 1 ≤ 9 ∧ 9 ≤ (11 : ℕ) ∧
    Even (support.sum (fun x ↦ x) + 9) ∧
    block ⊆ support ∧ block.sum (fun x ↦ x) = 9 ∧ 5 ∈ block ∧
    6 ∈ support \ block ∧ 5 < (6 : ℕ) ∧ 6 < (9 : ℕ) ∧
    9 - 6 = (3 : ℕ) ∧ 1 ≤ (3 : ℕ) ∧ 3 < (Icc 1 11 \ support).card ∧
    3 ∉ support ∧ residual.remaining = {7, 8, 10, 11} ∧
    residual.remaining.sum (fun x ↦ x) = 36 ∧
    residual.deficit ≤ residual.remaining.sum (fun x ↦ x) := by
  decide +kernel

/-- Kernel check that every exact-nine subset is the displayed block. -/
theorem exact_block_unique (A : Finset ℕ) (hA : A ⊆ support)
    (hsum : A.sum (fun x ↦ x) = 9) : A = block := by
  have hfinite : ∀ D ∈ support.powerset,
      D.sum (fun x ↦ x) = 9 → D = block := by decide +kernel
  exact hfinite A (mem_powerset.mpr hA) hsum

/-- Five is a global upper bound for members of every exact-nine block. -/
theorem global_exact_block_bound (A : Finset ℕ) (hA : A ⊆ support)
    (hsum : A.sum (fun x ↦ x) = 9) (x : ℕ) (hx : x ∈ A) : x ≤ 5 := by
  rw [exact_block_unique A hA hsum] at hx
  simp only [block, mem_insert, mem_singleton] at hx
  omega

/-- Three is not represented by any subset of the original support. -/
theorem original_subsum_gap (A : Finset ℕ) (hA : A ⊆ support) :
    A.sum (fun x ↦ x) ≠ 3 := by
  have hfinite : ∀ D ∈ support.powerset, D.sum (fun x ↦ x) ≠ 3 := by decide +kernel
  exact hfinite A (mem_powerset.mpr hA)

/-- The actual residual opening is losing. -/
theorem residual_loss : residual.value = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

/-- The losing residual opening is an actual nonterminal position. -/
theorem residual_nonterminal :
    ¬(GamePosition.afterOpening (support \ block) 6).IsTerminal := by
  decide +kernel

/-- The full dense maximal-block gap configuration, without any parent-loss assumption. -/
theorem full_branch_configuration :
    support ⊆ Icc 1 11 ∧ 2 * (Icc 1 11 \ support).card + 1 ≤ 9 ∧ 9 ≤ (11 : ℕ) ∧
    Even (support.sum (fun x ↦ x) + 9) ∧
    block ⊆ support ∧ block.sum (fun x ↦ x) = 9 ∧ 5 ∈ block ∧
    6 ∈ support \ block ∧ 5 < (6 : ℕ) ∧ 6 < (9 : ℕ) ∧
    1 ≤ 9 - (6 : ℕ) ∧ 9 - 6 < (Icc 1 11 \ support).card ∧
    (∀ A : Finset ℕ, A ⊆ support → A.sum (fun x ↦ x) = 9 → ∀ x ∈ A, x ≤ 5) ∧
    (∀ A : Finset ℕ, A ⊆ support → A.sum (fun x ↦ x) ≠ 9 - 6) ∧
    (afterOpening (support \ block) 6).value = .loss ∧
    ¬(GamePosition.afterOpening (support \ block) 6).IsTerminal := by
  obtain ⟨hS, _, _, hlarge, hdN, heven, hB, hsumB, hb, hw, hbw, hwd,
    _, ht, htsmall, _⟩ := arithmetic_premises
  exact ⟨hS, hlarge, hdN, heven, hB, hsumB, hb, hw, hbw, hwd, ht, htsmall,
    global_exact_block_bound, original_subsum_gap, residual_loss, residual_nonterminal⟩

/-- The continuing state is drawn. -/
theorem low_draw : low.value = .draw := by
  rw [← Position.eval_eq_value]
  decide +kernel

/-- Exact first-pick values; each value includes optimal play against every response. -/
theorem first_pick_values :
    low.moveOutcome 4 = .loss ∧ low.moveOutcome 5 = .loss ∧
    low.moveOutcome 7 = .loss ∧ low.moveOutcome 8 = .draw ∧
    low.moveOutcome 10 = .loss ∧ low.moveOutcome 11 = .loss := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num only [Position.moveOutcome, low]
  all_goals rw [← Position.eval_eq_value]
  all_goals decide +kernel

/-- Eight is the only legal first pick that avoids loss. -/
theorem unique_safe_first_pick (x : ℕ) (hx : x ∈ low.remaining) :
    low.moveOutcome x ≠ .loss ↔ x = 8 := by
  obtain ⟨h4, h5, h7, h8, h10, h11⟩ := first_pick_values
  have hremaining : low.remaining = {4, 5, 7, 8, 10, 11} := by decide +kernel
  rw [hremaining] at hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- Both entries through the exact block lose under optimal opposition. -/
theorem block_entries_lose (x : ℕ) (hx : x ∈ block) : low.moveOutcome x = .loss := by
  obtain ⟨h4, h5, _⟩ := first_pick_values
  simp only [block, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl <;> assumption

/-- A controller requiring its first continuing-state pick to lie in the block cannot be safe. -/
theorem no_safe_block_entry : ¬∃ x ∈ block, low.moveOutcome x ≠ .loss := by
  rintro ⟨x, hx, hsafe⟩
  exact hsafe (block_entries_lose x hx)

/-- The successor after pick eight is drawn from the new mover's perspective as well. -/
theorem after_eight_draw : afterEight.toPosition.value = .draw := by
  rw [← Position.eval_eq_value]
  decide +kernel

/-- The original mover has a nonlosing strategy after the safe pick. -/
theorem safe_after_eight : CanAvoidLoss .p1 afterEight := by
  rw [can_avoid_loss_iff_value, ite_eq_right (by decide : afterEight.toMove ≠ .p1)]
  rw [after_eight_draw]
  decide

/-- Every legal completed opponent turn preserves the original mover's nonloss strategy. -/
theorem every_opponent_turn_safe_after_eight {picks : List ℕ} {after : GamePosition}
    (turn : CompletedTurn afterEight picks after) : CanAvoidLoss .p1 after := by
  exact turn.safe_endpoint_of_can_avoid_loss (by decide) safe_after_eight

/-- The example is not a losing parent: pick six reaches the drawn continuing state. -/
theorem parent_nonloss : parent.value ≠ .loss := by
  intro hloss
  have hlow := Position.loss_after_continuing_pick parent (x := 6)
    (by decide) (by decide) (by decide) hloss
  have heq : parent.afterPick 6 = low := by decide +kernel
  rw [heq, low_draw] at hlow
  cases hlow

/-- Choosing one counter from each adjacent pair gives every total from 21 through 24. -/
theorem selector_totals :
    ((({4, 5} : Finset ℕ).product {7, 8}).product {10, 11}).image
      (fun p ↦ p.1.1 + p.1.2 + p.2) = Icc 21 24 := by
  decide +kernel

/-- The balanced quota is attained by the largest member of each adjacent pair. -/
theorem balanced_selector :
    ({5, 8, 11} : Finset ℕ) ⊆ low.remaining ∧
    ({5, 8, 11} : Finset ℕ).sum (fun x ↦ x) = 24 ∧
    2 * ({5, 8, 11} : Finset ℕ).sum (fun x ↦ x) =
      low.remaining.sum (fun x ↦ x) + low.deficit := by
  decide +kernel

/-- Every legal whole turn from the continuing state consists of a single pick. -/
theorem every_low_turn_singleton {mover : Player} {picks : List ℕ} {after : GamePosition}
    (turn : CompletedTurn ⟨low, mover⟩ picks after) :
    ∃ x ∈ low.remaining, picks = [x] := by
  cases turn with
  | finish position x legal catches => exact ⟨x, legal, rfl⟩
  | more position x xs after legal behind tail =>
      have hmin : ∀ y ∈ low.remaining, 4 ≤ y := by decide +kernel
      have hx := hmin x legal
      change x < 3 at behind
      omega

/-- A balanced selector total need not be the total of a legal whole turn. -/
theorem no_quota_completed_turn {mover : Player} {picks : List ℕ} {after : GamePosition}
    (turn : CompletedTurn ⟨low, mover⟩ picks after) : picks.sum ≠ 24 := by
  obtain ⟨x, hx, hpicks⟩ := every_low_turn_singleton turn
  have hmax : ∀ y ∈ low.remaining, y ≤ 11 := by decide +kernel
  have hxmax := hmax x hx
  rw [hpicks]
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

end CatchUp.DenseBlockEntryObstruction
