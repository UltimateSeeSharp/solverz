/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CompletedMargin.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.Parity
public import CatchUp.BoCowgill.CompletedTurn
public import CatchUp.BoCowgill.Earlier.SimulationSoundness

/-!
# Completed signed margins in Catch-Up

At a terminal state, notionally give every remaining counter to the trailing player.
This preserves the winner. Even effective totals turn a positive completed margin into
a margin of at least two. No strategy-translation closure is assumed or proved here.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- Fixed-player score margin after notionally giving the remainder to the current mover.
Only terminal positions represent completed games under this definition. -/
def GamePosition.completedMargin (p : GamePosition) (player : Player) : ℤ :=
  player.scoreCoefficient * (p.p1ScoreBalance +
    p.toMove.scoreCoefficient * (p.remaining.sum id : ℕ))

/-- Notional completion at a terminal position preserves all three outcomes. -/
theorem GamePosition.completion_sign (p : GamePosition) (player : Player)
    (ht : p.IsTerminal) :
    (p.terminalOutcomeFor player = .win ↔ 0 < p.completedMargin player) ∧
    (p.terminalOutcomeFor player = .draw ↔ p.completedMargin player = 0) ∧
    (p.terminalOutcomeFor player = .loss ↔ p.completedMargin player < 0) := by
  by_cases hz : p.deficit = 0
  · have he : p.remaining = ∅ := by
      rcases ht with he | hl
      · exact he
      · omega
    cases hp : p.toMove <;> cases player <;>
      simp [GamePosition.terminalOutcomeFor, GamePosition.completedMargin,
        GamePosition.p1ScoreBalance, Player.scoreCoefficient, hp, he, hz]
  · have hl : p.remaining.sum (fun x ↦ x) < p.deficit := by
      rcases ht with he | hl
      · simpa [he] using Nat.pos_of_ne_zero hz
      · exact hl
    cases hp : p.toMove <;> cases player <;>
      simp [GamePosition.terminalOutcomeFor, GamePosition.completedMargin,
        GamePosition.p1ScoreBalance, Player.scoreCoefficient, hp, hz, -Nat.cast_sum] <;>
      omega

/-- Effective parity is also the parity of a fixed-player completed margin. -/
theorem GamePosition.completed_margin_even (p : GamePosition) (player : Player)
    (he : (p.deficit + p.remaining.sum (fun x ↦ x)) % 2 = 0) :
    p.completedMargin player % 2 = 0 := by
  cases hp : p.toMove <;> cases player <;>
    simp [GamePosition.completedMargin, GamePosition.p1ScoreBalance,
      Player.scoreCoefficient, hp, -Nat.cast_sum] <;> omega

/-- A completed win with even effective total has margin at least two. -/
theorem GamePosition.completed_win_margin_ge_two (p : GamePosition) (player : Player)
    (ht : p.IsTerminal) (hw : p.terminalOutcomeFor player = .win)
    (he : (p.deficit + p.remaining.sum (fun x ↦ x)) % 2 = 0) :
    2 ≤ p.completedMargin player := by
  have hpos := (p.completion_sign player ht).1.mp hw
  have hmod := p.completed_margin_even player he
  omega

/-- Losing at most two completed-margin points transfers an even-total win to a nonloss. -/
theorem completed_margin_transfer (u v : GamePosition) (player : Player)
    (hu : u.IsTerminal) (hv : v.IsTerminal)
    (hw : v.terminalOutcomeFor player = .win)
    (he : (v.deficit + v.remaining.sum (fun x ↦ x)) % 2 = 0)
    (hm : v.completedMargin player - 2 ≤ u.completedMargin player) :
    u.terminalOutcomeFor player ≠ .loss := by
  have htwo := v.completed_win_margin_ge_two player hv hw he
  intro hl
  have hneg := (u.completion_sign player hu).2.2.mp hl
  omega

/-- Erasing one and two disjoint consecutive pairs leaves even effective total at deficit one. -/
theorem erase_two_pairs_even (S : Finset ℕ) (a c : ℕ)
    (h1 : 1 ∈ S) (ha : a ∈ S.erase 1)
    (ha1 : a + 1 ∈ (S.erase 1).erase a)
    (hc : c ∈ ((S.erase 1).erase a).erase (a + 1))
    (hc1 : c + 1 ∈ (((S.erase 1).erase a).erase (a + 1)).erase c)
    (he : S.sum (fun x ↦ x) % 2 = 0) :
    (1 + (((((S.erase 1).erase a).erase (a + 1)).erase c).erase (c + 1)).sum
      (fun x ↦ x)) % 2 = 0 := by
  have e1 := Finset.sum_erase_add S (fun x ↦ x) h1
  have e2 := Finset.sum_erase_add (S.erase 1) (fun x ↦ x) ha
  have e3 := Finset.sum_erase_add ((S.erase 1).erase a) (fun x ↦ x) ha1
  have e4 := Finset.sum_erase_add (((S.erase 1).erase a).erase (a + 1)) (fun x ↦ x) hc
  have e5 := Finset.sum_erase_add ((((S.erase 1).erase a).erase (a + 1)).erase c)
    (fun x ↦ x) hc1
  omega

namespace GamePosition

/-- Signed score contributions recorded when each pick occurs, with its actual mover. -/
def signedPicks (player : Player) : GamePosition → List ℕ → ℤ
  | _, [] => 0
  | p, x :: xs => player.scoreCoefficient * p.toMove.scoreCoefficient * (x : ℤ) +
      signedPicks player (p.afterPick x) xs

/-- Historical signed contributions telescope to the fixed-player score balance. -/
theorem signed_picks_balance (p : GamePosition) (player : Player) (xs : List ℕ) :
    player.scoreCoefficient * (p.afterPicks xs).p1ScoreBalance =
      player.scoreCoefficient * p.p1ScoreBalance + signedPicks player p xs := by
  induction xs generalizing p with
  | nil => simp [signedPicks]
  | cons x xs ih =>
      simp only [after_picks_cons, signedPicks, ih, p1_score_balance_after_pick]
      ring

/-- Completion adds only the trailing player's remaining-counter credit to the historical ledger. -/
theorem completed_margin_ledger (p : GamePosition) (player : Player) (xs : List ℕ) :
    (p.afterPicks xs).completedMargin player =
      player.scoreCoefficient * p.p1ScoreBalance + signedPicks player p xs +
        player.scoreCoefficient * (p.afterPicks xs).toMove.scoreCoefficient *
          ((p.afterPicks xs).remaining.sum id : ℕ) := by
  unfold completedMargin
  rw [mul_add, signed_picks_balance]
  ring

/-- Legal traces preserve effective-total parity, including asynchronous multi-pick macros. -/
theorem PickTrace.effective_parity {p q : GamePosition} {xs : List ℕ}
    (trace : PickTrace p xs q) :
    (q.deficit + q.remaining.sum (fun x ↦ x)) % 2 =
      (p.deficit + p.remaining.sum (fun x ↦ x)) % 2 := by
  induction trace with
  | nil => rfl
  | cons p x xs q hs tail ih =>
      rcases hs.2 with ⟨z, hz, he⟩
      rw [he] at ih
      exact ih.trans (p.toPosition.mod_eq_two_deficit_add_sum_after_pick hz)

/-- A legal trace cannot replenish the counter supply. -/
theorem PickTrace.remaining_card_le {p q : GamePosition} {xs : List ℕ}
    (trace : PickTrace p xs q) : q.remaining.card ≤ p.remaining.card := by
  induction trace with
  | nil => rfl
  | cons p x xs q hs tail ih =>
      rcases hs.2 with ⟨z, hz, he⟩
      rw [he] at ih
      exact ih.trans (Nat.le_of_lt (p.remaining_card_after_pick_lt z hz))
end GamePosition

end CatchUp
