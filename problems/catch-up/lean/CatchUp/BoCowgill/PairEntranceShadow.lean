/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/PairEntranceShadow.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.CompletedTurn
public import CatchUp.BoCowgill.ExactSumLossObstruction

/-!
# A reserved counter shadows every opponent turn that avoids it

The reply wins whenever the opponent's whole-turn sum differs from the losing
shadow deficit. At equality the same reply loses because it ties and swaps
perspectives. No density or bounded-cardinality assumption is used.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.PairEntranceShadow

open CatchUp (Position.loss_after_erasing_subsum)

/-- A losing shadow remains losing after any below-deficit subset, including a terminal shadow. -/
theorem loss_after_subsum
    (C Y : Finset ℕ) (w : ℕ) (hY : Y ⊆ C)
    (hbelow : Y.sum (fun x ↦ x) < w) (hloss : (⟨C, w⟩ : Position).value = .loss) :
    (⟨C \ Y, w - Y.sum (fun x ↦ x)⟩ : Position).value = .loss := by
  by_cases hterminal : C.sum (fun x ↦ x) < w
  · have hsum := Finset.sum_sdiff (f := fun x : ℕ ↦ x) hY
    have hchild : (C \ Y).sum (fun x ↦ x) < w - Y.sum (fun x ↦ x) := by omega
    rw [Position.value.eq_def]
    by_cases he : C \ Y = ∅
    · simp [he, show w - Y.sum (fun x ↦ x) ≠ 0 by omega]
    · simp [he, hchild]
  · exact Position.loss_after_erasing_subsum C Y w hY hbelow hterminal hloss

/-- Every legal completed turn from a loss leaves a win for the new mover. -/
theorem turn_endpoint_win_of_loss
    (position : Position) (Y : Finset ℕ) (final : ℕ)
    (turn : TurnSet ⟨position, .p1⟩ Y final) (hloss : position.value = .loss) :
    (completedTurnEndpoint ⟨position, .p1⟩ Y).toPosition.value = .win := by
  have hremaining : position.remaining ≠ ∅ := by
    exact Finset.ne_empty_of_mem (turn.chosen_subset turn.final_mem)
  have hsum := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x) turn.chosen_subset
  change Y.sum (fun x ↦ x) ≤ position.remaining.sum (fun x ↦ x) at hsum
  have hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit := by
    have hc := turn.catches
    change position.deficit ≤ Y.sum (fun x ↦ x) at hc
    omega
  by_contra hnot
  have hsafe := (position.value_ne_loss_iff_exists_turn_set hremaining hcatch).mpr
    ⟨Y, final, turn, hnot⟩
  exact hsafe hloss

/-- The reserved-counter reply has an exact outcome for every complete turn avoiding the reserve.
The exceptional total equals the shadow deficit: the reply then ties and loses. -/
theorem reserve_reply_outcome
    (C Y : Finset ℕ) (b c final : ℕ) (hb : b ∉ C)
    (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final) (hbY : b ∉ Y) :
    (⟨insert b (C \ Y), Y.sum (fun x ↦ x) - c⟩ : Position).moveOutcome b =
      if Y.sum (fun x ↦ x) = b + c then .loss else .win := by
  let y := Y.sum (fun x ↦ x)
  change (⟨insert b (C \ Y), y - c⟩ : Position).moveOutcome b =
    if y = b + c then .loss else .win
  have hY : Y ⊆ C := by
    intro x hx
    have hm := turn.chosen_subset hx
    change x ∈ insert b C at hm
    rcases mem_insert.mp hm with he | hm
    · subst x
      exact False.elim (hbY hx)
    · exact hm
  have hyc : c ≤ y := turn.catches
  have hberase : (insert b (C \ Y)).erase b = C \ Y := by
    apply Finset.erase_insert
    intro hm
    exact hb (mem_sdiff.mp hm).1
  by_cases hbelow : y < b + c
  · have hp := loss_after_subsum C Y (b + c) hY hbelow hloss
    have hnot : ¬ b < y - c := by omega
    have hdef : b - (y - c) = b + c - y := by omega
    rw [ite_eq_right (by omega)]
    simp only [Position.moveOutcome, Position.afterPick, hnot, ite_false, hberase, hdef]
    rw [hp]
    rfl
  · have hshadow : TurnSet ⟨⟨C, b + c⟩, .p1⟩ Y final := by
      refine ⟨turn.final_mem, hY, by change b + c ≤ y; omega, ?_⟩
      rcases turn.preparation_below with he | hprep
      · exact Or.inl he
      · right
        change (Y.erase final).sum (fun x ↦ x) < b + c
        change (Y.erase final).sum (fun x ↦ x) < c at hprep
        omega
    have hwin := turn_endpoint_win_of_loss ⟨C, b + c⟩ Y final hshadow hloss
    change (⟨C \ Y, y - (b + c)⟩ : Position).value = .win at hwin
    by_cases he : y = b + c
    · have hdef : y - c = b := by omega
      have hzero : y - (b + c) = 0 := by omega
      rw [hzero] at hwin
      rw [ite_eq_left he]
      simp only [Position.moveOutcome, Position.afterPick, hdef, Nat.lt_irrefl,
        ite_false, hberase, Nat.sub_self, hwin, Outcome.neg]
    · have hlt : b < y - c := by omega
      have hdef : y - c - b = y - (b + c) := by omega
      rw [ite_eq_right he]
      simp only [Position.moveOutcome, Position.afterPick, hlt, ite_true, hberase, hdef, hwin]

/-- An opponent turn avoiding the reserve leaves exactly the advertised actual position. -/
theorem reserve_endpoint_eq
    (C Y : Finset ℕ) (b c : ℕ) (hbY : b ∉ Y) :
    (completedTurnEndpoint ⟨⟨insert b C, c⟩, .p1⟩ Y).toPosition =
      ⟨insert b (C \ Y), Y.sum (fun x ↦ x) - c⟩ := by
  change (⟨insert b C \ Y, Y.sum (fun x ↦ x) - c⟩ : Position) = _
  congr 1
  ext x
  simp only [mem_sdiff, mem_insert]
  by_cases he : x = b
  · subst x
    simp [hbY]
  · simp [he]

/-- The piecewise contract at the genuine completed-turn endpoint. -/
theorem reserve_reply_at_endpoint
    (C Y : Finset ℕ) (b c final : ℕ) (hb : b ∉ C)
    (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final) (hbY : b ∉ Y) :
    (completedTurnEndpoint ⟨⟨insert b C, c⟩, .p1⟩ Y).toPosition.moveOutcome b =
      if Y.sum (fun x ↦ x) = b + c then .loss else .win := by
  rw [reserve_endpoint_eq C Y b c hbY]
  exact reserve_reply_outcome C Y b c final hb hloss turn hbY

/-- Away from equality the actual endpoint wins, with a legal nonterminal reserve reply. -/
theorem endpoint_win_of_total_ne
    (C Y : Finset ℕ) (b c final : ℕ) (hb : b ∉ C)
    (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final) (hbY : b ∉ Y)
    (hne : Y.sum (fun x ↦ x) ≠ b + c) :
    (⟨insert b (C \ Y), Y.sum (fun x ↦ x) - c⟩ : Position).value = .win := by
  let R := C \ Y
  let y := Y.sum (fun x ↦ x)
  let position : Position := ⟨insert b R, y - c⟩
  have hmove : position.moveOutcome b = .win := by
    simpa only [ite_eq_right hne] using reserve_reply_outcome C Y b c final hb hloss turn hbY
  have hbR : b ∉ R := by intro hm; exact hb (mem_sdiff.mp hm).1
  have herase : (insert b R).erase b = R := Finset.erase_insert hbR
  have hmem : b ∈ position.remaining := by simp [position]
  have hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit := by
    intro hterminal
    change (insert b R).sum (fun x ↦ x) < y - c at hterminal
    have hsum := Finset.sum_insert (f := fun x : ℕ ↦ x) hbR
    have hlt : b < y - c := by omega
    have hchild : R.sum (fun x ↦ x) < y - c - b := by omega
    have hchildLoss : (⟨R, y - c - b⟩ : Position).value = .loss := by
      rw [Position.value.eq_def]
      by_cases he : R = ∅
      · simp [he, show y - c - b ≠ 0 by omega]
      · simp [he, hchild]
    have hbad : position.moveOutcome b = .loss := by
      change (⟨insert b R, y - c⟩ : Position).moveOutcome b = .loss
      simp only [Position.moveOutcome, Position.afterPick, hlt, ite_true, herase]
      exact hchildLoss
    rw [hbad] at hmove
    cases hmove
  by_contra hnot
  rw [position.value_eq_best_move_outcome (Finset.ne_empty_of_mem hmem) hcatch] at hnot
  have hall := (Outcome.best_ne_win_iff _).mp hnot
  apply hall (position.moveOutcome b)
  · exact List.mem_map.mpr ⟨⟨b, hmem⟩, by simp, rfl⟩
  · exact hmove

/-- Every ordered completed opponent turn avoiding the reserve obeys the same exact contract. -/
theorem reserve_reply_after_completed_turn
    (C : Finset ℕ) (b c final : ℕ) (preparation : List ℕ) (after : GamePosition)
    (hb : b ∉ C) (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (trace : CompletedTurn ⟨⟨insert b C, c⟩, .p1⟩ (preparation ++ [final]) after)
    (hbY : b ∉ insert final preparation.toFinset) :
    after.toPosition.moveOutcome b =
      if (preparation ++ [final]).sum = b + c then .loss else .win := by
  let Y := insert final preparation.toFinset
  have hset : (preparation ++ [final]).toFinset = Y := by
    simp [Y]
  have hsum : Y.sum (fun x ↦ x) = (preparation ++ [final]).sum := by
    have hs := List.sum_toFinset (fun x : ℕ ↦ x) trace.picks_nodup
    simpa [hset] using hs
  have he : after = completedTurnEndpoint ⟨⟨insert b C, c⟩, .p1⟩ Y := by
    simpa only [hset] using trace.after_eq_endpoint
  have hp := reserve_reply_at_endpoint C Y b c final hb hloss trace.turn_set hbY
  rw [← he, hsum] at hp
  exact hp

end CatchUp.PairEntranceShadow
