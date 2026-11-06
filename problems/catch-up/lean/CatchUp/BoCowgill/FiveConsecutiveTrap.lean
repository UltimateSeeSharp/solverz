/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/FiveConsecutiveTrap.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.TopFourClassification
public import CatchUp.BoCowgill.WinningOpening
public import CatchUp.BoCowgill.Earlier.LowerRayExactDeficit

/-!
# A Reachable Five-Consecutive-Counter Trap in Catch-Up

Five consecutive counters beginning at least at `4` form a first-player win when play begins tied.
Nevertheless, in every interval game of size `4 * k`, `k ≥ 2`, a legal history after opening `3`
reaches exactly the tied top five counters with player one to move. This gives an infinite family of
reachable winning traps for block-clearing strategies; it does not assert that optimal play must
enter the trap.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

private theorem best_eq_win_iff_for_five_band (outcomes : List Outcome) :
    Outcome.best outcomes = .win ↔ ∃ outcome ∈ outcomes, outcome = .win := by
  rw [← not_iff_not]
  simp
  constructor
  · intro hall hmem
    exact hall .win hmem rfl
  · intro hnot outcome hmem heq
    subst outcome
    exact hnot hmem

private theorem position_value_eq_win_iff_for_five_band (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit) :
    position.value = .win ↔
      ∃ x ∈ position.remaining, position.moveOutcome x = .win := by
  rw [Position.value_eq_best_move_outcome position hremaining hcatch,
    best_eq_win_iff_for_five_band]
  simp [Position.moveOutcome]

/-- Five consecutive counters beginning at least at `4` form a first-player win. -/
theorem value_five_consecutive_eq_win (a : ℕ) (ha : 4 ≤ a) :
    value (Finset.Icc a (a + 4)) = .win := by
  let remaining := Finset.Icc a (a + 4)
  have hremaining : remaining.Nonempty := Finset.nonempty_Icc.mpr (by omega)
  rw [value_eq_win_iff_exists_winning_opening remaining hremaining]
  refine ⟨a, by simp [remaining], ?_⟩
  have herase : remaining.erase a = {a + 1, a + 2, a + 3, a + 4} := by
    ext counter
    simp [remaining]
    omega
  change Position.value ⟨remaining.erase a, a⟩ = .loss
  rw [herase, CatchUpSearch.TopFourClassification.value_top_four
    (a + 1) a (by omega) (by omega)]
  simp only [CatchUpSearch.TopFourClassification.topFourFormula]
  split_ifs <;> simp_all

/-- Five consecutive counters beginning at least at `6` form a win for the player to move at
every deficit no greater than the second counter. -/
theorem Position.value_five_consecutive_deficit_band (a deficit : ℕ)
    (ha : 6 ≤ a) (hdeficit : deficit ≤ a + 1) :
    Position.value ⟨Finset.Icc a (a + 4), deficit⟩ = .win := by
  have haMem : a ∈ Finset.Icc a (a + 4) := by simp
  have hremaining : Finset.Icc a (a + 4) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨a, haMem⟩
  have haNextMem : a + 1 ∈ Finset.Icc a (a + 4) := by simp
  have hsum : a + 1 ≤ (Finset.Icc a (a + 4)).sum (fun x ↦ x) :=
    Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) haNextMem
  have hcatch : ¬ (Finset.Icc a (a + 4)).sum (fun x ↦ x) < deficit := by
    omega
  apply (position_value_eq_win_iff_for_five_band
    ⟨Finset.Icc a (a + 4), deficit⟩ hremaining hcatch).2
  by_cases hsmall : deficit ≤ 3
  · refine ⟨a, haMem, ?_⟩
    have hnotContinue : ¬ a < deficit := by omega
    have herase : (Finset.Icc a (a + 4)).erase a =
        {a + 1, a + 2, a + 3, a + 4} := by
      ext x
      simp
      omega
    simp only [Position.moveOutcome, Position.afterPick, hnotContinue, ite_false]
    rw [herase, CatchUpSearch.TopFourClassification.value_top_four
      (a + 1) (a - deficit) (by omega) (by omega)]
    have hdiffNonzero : a - deficit ≠ 0 := by omega
    have hdiffNeTwo : a - deficit ≠ 2 := by omega
    have hdiffLe : a - deficit ≤ a + 1 := by omega
    simp [CatchUpSearch.TopFourClassification.topFourFormula, hdiffNonzero,
      hdiffNeTwo, hdiffLe, Outcome.neg]
  · have htopMem : a + 4 ∈ Finset.Icc a (a + 4) := by simp
    refine ⟨a + 4, htopMem, ?_⟩
    have hnotContinue : ¬ a + 4 < deficit := by omega
    have herase : (Finset.Icc a (a + 4)).erase (a + 4) =
        {a, a + 1, a + 2, a + 3} := by
      ext x
      simp
      omega
    simp only [Position.moveOutcome, Position.afterPick, hnotContinue, ite_false]
    rw [herase, CatchUpSearch.TopFourClassification.value_top_four
      a (a + 4 - deficit) (by omega) (by omega)]
    have hdiffNonzero : a + 4 - deficit ≠ 0 := by omega
    have hdiffNeTwo : a + 4 - deficit ≠ 2 := by omega
    have hdiffLe : a + 4 - deficit ≤ a := by omega
    simp [CatchUpSearch.TopFourClassification.topFourFormula, hdiffNonzero,
      hdiffNeTwo, hdiffLe, Outcome.neg]

private def tiedInterval (low high : ℕ) : GamePosition where
  remaining := Finset.Icc low high
  deficit := 0
  toMove := .p1

private theorem step_after_pick_of_mem_of_deficit_le
    (position : GamePosition) (x : ℕ) (hx : x ∈ position.remaining)
    (hdeficit : position.deficit ≤ x) :
    position.Step (position.afterPick x) := by
  apply position.step_after_pick x
  · rw [GamePosition.not_is_terminal_iff]
    constructor
    · exact Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩
    · have hsum : x ≤ position.remaining.sum (fun y ↦ y) :=
        Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
      omega
  · exact hx

private theorem four_picks_from_tied_interval (low high : ℕ) :
    ((((tiedInterval low high).afterPick low).afterPick (low + 1)).afterPick (low + 3)).afterPick
        (low + 2) = tiedInterval (low + 4) high := by
  have hremaining :
      (((Finset.Ioc low high).erase (low + 1)).erase (low + 3)).erase
          (low + 2) = Finset.Icc (low + 4) high := by
    ext x
    simp
    omega
  have hsecondDeficit : low + 1 - low = 1 := by omega
  have hthirdDeficit : low + 3 - 1 = low + 2 := by omega
  simp [tiedInterval, GamePosition.afterPick, Position.afterPick, hremaining,
    hsecondDeficit, hthirdDeficit]

private theorem consume_quartet (low high : ℕ) (hhigh : low + 3 ≤ high) :
    Relation.ReflTransGen GamePosition.Step (tiedInterval low high)
      (tiedInterval (low + 4) high) := by
  let p0 := tiedInterval low high
  let p1 := p0.afterPick low
  let p2 := p1.afterPick (low + 1)
  let p3 := p2.afterPick (low + 3)
  let p4 := p3.afterPick (low + 2)
  have hmem0 : low ∈ p0.remaining := by
    simp [p0, tiedInterval]
    omega
  have hstep0 : p0.Step p1 := by
    apply step_after_pick_of_mem_of_deficit_le p0 low hmem0
    simp [p0, tiedInterval]
  have hmem1 : low + 1 ∈ p1.remaining := by
    simp [p1, p0, tiedInterval, GamePosition.afterPick, Position.afterPick]
    omega
  have hstep1 : p1.Step p2 := by
    apply step_after_pick_of_mem_of_deficit_le p1 (low + 1) hmem1
    simp [p1, p0, tiedInterval, GamePosition.afterPick, Position.afterPick]
  have hmem2 : low + 3 ∈ p2.remaining := by
    simp [p2, p1, p0, tiedInterval, GamePosition.afterPick, Position.afterPick]
    omega
  have hstep2 : p2.Step p3 := by
    apply step_after_pick_of_mem_of_deficit_le p2 (low + 3) hmem2
    simp [p2, p1, p0, tiedInterval, GamePosition.afterPick, Position.afterPick]
  have hmem3 : low + 2 ∈ p3.remaining := by
    simp [p3, p2, p1, p0, tiedInterval, GamePosition.afterPick, Position.afterPick]
    omega
  have hstep3 : p3.Step p4 := by
    apply step_after_pick_of_mem_of_deficit_le p3 (low + 2) hmem3
    simp [p3, p2, p1, p0, tiedInterval, GamePosition.afterPick, Position.afterPick]
  have hp4 : p4 = tiedInterval (low + 4) high := by
    simpa [p4, p3, p2, p1, p0] using four_picks_from_tied_interval low high
  have htrace : Relation.ReflTransGen GamePosition.Step p0 p4 :=
    (((Relation.ReflTransGen.refl).tail hstep0).tail hstep1).tail hstep2 |>.tail hstep3
  rw [hp4] at htrace
  simpa [p0] using htrace

private theorem two_picks_after_opening_three (high : ℕ) :
    ((GamePosition.afterOpening (Finset.Icc 1 high) 3).afterPick 1).afterPick 2 =
      tiedInterval 4 high := by
  have hremaining : (((Finset.Icc 1 high).erase 3).erase 1).erase 2 =
      Finset.Icc 4 high := by
    ext x
    simp
    omega
  simp [GamePosition.afterOpening, afterOpening, tiedInterval, GamePosition.afterPick,
    Position.afterPick, hremaining]

private theorem opening_three_to_tied_four (high : ℕ) (hhigh : 4 ≤ high) :
    Relation.ReflTransGen GamePosition.Step
      (GamePosition.afterOpening (Finset.Icc 1 high) 3) (tiedInterval 4 high) := by
  let p0 := GamePosition.afterOpening (Finset.Icc 1 high) 3
  let p1 := p0.afterPick 1
  let p2 := p1.afterPick 2
  have hmem0 : 1 ∈ p0.remaining := by
    simp [p0, GamePosition.afterOpening, afterOpening]
    omega
  have hstep0 : p0.Step p1 := by
    apply p0.step_after_pick 1
    · rw [GamePosition.not_is_terminal_iff]
      constructor
      · exact Finset.nonempty_iff_ne_empty.mp ⟨1, hmem0⟩
      · have hmem4 : 4 ∈ p0.remaining := by
          simp [p0, GamePosition.afterOpening, afterOpening]
          omega
        have hsum : 4 ≤ p0.remaining.sum (fun x ↦ x) :=
          Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hmem4
        have hdeficit : p0.deficit = 3 := by
          simp [p0, GamePosition.afterOpening, afterOpening]
        omega
    · exact hmem0
  have hmem1 : 2 ∈ p1.remaining := by
    simp [p1, p0, GamePosition.afterOpening, afterOpening, GamePosition.afterPick,
      Position.afterPick]
    omega
  have hstep1 : p1.Step p2 := by
    apply step_after_pick_of_mem_of_deficit_le p1 2 hmem1
    simp [p1, p0, GamePosition.afterOpening, afterOpening, GamePosition.afterPick,
      Position.afterPick]
  have hp2 : p2 = tiedInterval 4 high := by
    simpa [p2, p1, p0] using two_picks_after_opening_three high
  have htrace : Relation.ReflTransGen GamePosition.Step p0 p2 :=
    (Relation.ReflTransGen.refl.tail hstep0).tail hstep1
  rw [hp2] at htrace
  simpa [p0] using htrace

private theorem consume_quartets (high count : ℕ) (hhigh : 4 + 4 * count ≤ high) :
    Relation.ReflTransGen GamePosition.Step (tiedInterval 4 high)
      (tiedInterval (4 + 4 * count) high) := by
  induction count with
  | zero =>
      simpa using (Relation.ReflTransGen.refl :
        Relation.ReflTransGen GamePosition.Step (tiedInterval 4 high) (tiedInterval 4 high))
  | succ count ih =>
      have hprevious : 4 + 4 * count ≤ high := by omega
      have hendpoint : (4 + 4 * count) + 3 ≤ high := by omega
      have hprefix := ih hprevious
      have hblock := consume_quartet (4 + 4 * count) high hendpoint
      have htrace := hprefix.trans hblock
      simpa [Nat.mul_succ, Nat.add_assoc] using htrace

/-- Opening `3` in the game of size `4 * k` admits a legal history reaching the tied top five
counters with player one to move. -/
theorem reachable_tied_top_five (k : ℕ) (hk : 2 ≤ k) :
    ReachableFromOpening (4 * k) 3
      { remaining := Finset.Icc (4 * k - 4) (4 * k), deficit := 0, toMove := .p1 } := by
  change ReachableFromOpening (4 * k) 3 (tiedInterval (4 * k - 4) (4 * k))
  constructor
  · simp
    omega
  · have hfour : 4 ≤ 4 * k := by omega
    have hcount : 4 + 4 * (k - 2) ≤ 4 * k := by omega
    have hbase := opening_three_to_tied_four (4 * k) hfour
    have hblocks := consume_quartets (4 * k) (k - 2) hcount
    have htrace := hbase.trans hblocks
    have hkDecomp : k = (k - 2) + 2 := by omega
    have hlow : 4 + 4 * (k - 2) = 4 * k - 4 := by
      rw [hkDecomp]
      omega
    rw [hlow] at htrace
    exact htrace

/-- The tied top-five position reached above is winning for player one. -/
theorem tied_top_five_value_eq_win (k : ℕ) (hk : 2 ≤ k) :
    Position.value ⟨Finset.Icc (4 * k - 4) (4 * k), 0⟩ = .win := by
  rw [position_value_zero_deficit_eq_value]
  have hstart : 4 ≤ 4 * k - 4 := by omega
  have hend : 4 * k = (4 * k - 4) + 4 := by omega
  rw [hend]
  exact value_five_consecutive_eq_win (4 * k - 4) hstart

/-- Every interval game of size `4 * k`, for `k ≥ 2`, has a legal history after opening `3`
that reaches a player-one win on exactly the tied top five counters. -/
theorem reachable_winning_tied_top_five (k : ℕ) (hk : 2 ≤ k) :
    ReachableFromOpening (4 * k) 3
        { remaining := Finset.Icc (4 * k - 4) (4 * k), deficit := 0, toMove := .p1 } ∧
      Position.value ⟨Finset.Icc (4 * k - 4) (4 * k), 0⟩ = .win := by
  exact ⟨reachable_tied_top_five k hk, tied_top_five_value_eq_win k hk⟩

end CatchUp
