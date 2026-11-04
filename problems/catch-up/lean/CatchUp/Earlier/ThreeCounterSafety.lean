/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/ThreeCounterSafety.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Reference

/-!
# A parametric Catch-Up three-counter safety theorem

This research module proves the explicit three-counter endgame family discovered by the
four-counter forcing-basin experiments.  Unlike the discovery predicate, the theorem below does
not consult a solver outcome: its hypotheses are only inequalities between the three remaining
counters and the current deficit.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.ThreeCounterSafety

open CatchUp

private theorem other_other (player : Player) : player.other.other = player := by
  cases player <;> rfl

private theorem other_ne_self (player : Player) : player.other ≠ player := by
  cases player <;> decide

/-- An empty position is safe for a player when the opponent is nominally next to move. -/
private theorem can_avoid_loss_empty_other (owner : Player) (deficit : ℕ) :
    CanAvoidLoss owner
      { remaining := ∅
        deficit
        toMove := owner.other } := by
  have hterminal :
      ({ remaining := ∅, deficit, toMove := owner.other } : GamePosition).IsTerminal :=
    GamePosition.is_terminal_of_remaining_eq_empty _ rfl
  apply (can_avoid_loss_iff_terminal_outcome_ne_loss owner _ hterminal).2
  by_cases hdeficit : deficit = 0
  · simp [GamePosition.terminalOutcomeFor, hdeficit]
  · simp [GamePosition.terminalOutcomeFor, hdeficit]

/-- A tied empty position is safe regardless of which player is nominally next to move. -/
private theorem can_avoid_loss_empty_zero (owner toMove : Player) :
    CanAvoidLoss owner
      { remaining := ∅
        deficit := 0
        toMove } := by
  have hterminal :
      ({ remaining := ∅, deficit := 0, toMove } : GamePosition).IsTerminal :=
    GamePosition.is_terminal_of_remaining_eq_empty _ rfl
  apply (can_avoid_loss_iff_terminal_outcome_ne_loss owner _ hterminal).2
  simp [GamePosition.terminalOutcomeFor]

/-- If the owner can catch up with the only counter, taking it avoids a loss. -/
private theorem can_avoid_loss_singleton_owner_of_le (owner : Player) (counter deficit : ℕ)
    (hcatch : deficit ≤ counter) :
    CanAvoidLoss owner
      { remaining := {counter}
        deficit
        toMove := owner } := by
  let position : GamePosition :=
    { remaining := {counter}
      deficit
      toMove := owner }
  have hterminal : ¬position.IsTerminal := by
    simp [position, GamePosition.IsTerminal]
    omega
  apply (can_avoid_loss_iff_exists_safe_move owner position hterminal rfl).2
  refine ⟨counter, by simp [position, GamePosition.LegalMove], ?_⟩
  simpa [position, GamePosition.afterPick, Position.afterPick, not_lt_of_ge hcatch] using
    can_avoid_loss_empty_other owner (counter - deficit)

/-- If the only counter cannot overcome the opponent's deficit, the owner cannot lose. -/
private theorem can_avoid_loss_singleton_other_of_le (owner : Player) (counter deficit : ℕ)
    (hsafe : counter ≤ deficit) :
    CanAvoidLoss owner
      { remaining := {counter}
        deficit
        toMove := owner.other } := by
  let position : GamePosition :=
    { remaining := {counter}
      deficit
      toMove := owner.other }
  by_cases hstrict : counter < deficit
  · have hterminal : position.IsTerminal := by
      apply GamePosition.is_terminal_of_sum_lt_deficit
      simpa [position] using hstrict
    apply (can_avoid_loss_iff_terminal_outcome_ne_loss owner position hterminal).2
    have hdeficit : deficit ≠ 0 := by omega
    simp [position, GamePosition.terminalOutcomeFor, hdeficit]
  · have heq : deficit = counter := by omega
    have hterminal : ¬position.IsTerminal := by
      simp [position, GamePosition.IsTerminal, heq]
    apply (can_avoid_loss_iff_forall_safe_moves owner position hterminal
      (other_ne_self owner)).2
    intro chosen hchosen
    have hchosenEq : chosen = counter := by
      simpa [position, GamePosition.LegalMove] using hchosen
    subst chosen
    simpa [position, GamePosition.afterPick, Position.afterPick, heq, other_other] using
      can_avoid_loss_empty_zero owner owner

/--
At an owner node with two counters, taking the larger one is safe when the smaller counter is no
larger than the opponent's resulting deficit.
-/
private theorem can_avoid_loss_pair_owner_take_upper (owner : Player) (lower upper deficit : ℕ)
    (hlowerUpper : lower < upper) (hcatch : deficit ≤ upper)
    (hlowerSafe : lower ≤ upper - deficit) :
    CanAvoidLoss owner
      { remaining := {lower, upper}
        deficit
        toMove := owner } := by
  let position : GamePosition :=
    { remaining := {lower, upper}
      deficit
      toMove := owner }
  have hterminal : ¬position.IsTerminal := by
    simp [position, GamePosition.IsTerminal, ne_of_lt hlowerUpper]
    omega
  apply (can_avoid_loss_iff_exists_safe_move owner position hterminal rfl).2
  refine ⟨upper, by simp [position, GamePosition.LegalMove], ?_⟩
  have herase : ({lower, upper} : Finset ℕ).erase upper = {lower} := by
    ext counter
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl | rfl⟩
      · rfl
      · contradiction
    · rintro rfl
      exact ⟨by omega, Or.inl rfl⟩
  have hsafe := can_avoid_loss_singleton_other_of_le owner lower (upper - deficit) hlowerSafe
  simpa [position, GamePosition.afterPick, Position.afterPick, not_lt_of_ge hcatch,
    herase, other_other] using hsafe

/--
At an owner node with two counters, the owner may take the lower counter, remain behind, and then
take the upper counter to finish the turn safely.
-/
private theorem can_avoid_loss_pair_owner_take_both (owner : Player) (lower upper deficit : ℕ)
    (hlowerUpper : lower < upper) (hcontinue : lower < deficit)
    (hcatch : deficit - lower ≤ upper) :
    CanAvoidLoss owner
      { remaining := {lower, upper}
        deficit
        toMove := owner } := by
  let position : GamePosition :=
    { remaining := {lower, upper}
      deficit
      toMove := owner }
  have hterminal : ¬position.IsTerminal := by
    simp [position, GamePosition.IsTerminal, ne_of_lt hlowerUpper]
    omega
  apply (can_avoid_loss_iff_exists_safe_move owner position hterminal rfl).2
  refine ⟨lower, by simp [position, GamePosition.LegalMove], ?_⟩
  have hsafe :=
    can_avoid_loss_singleton_owner_of_le owner upper (deficit - lower) hcatch
  simpa [position, GamePosition.afterPick, Position.afterPick, hcontinue, ne_of_lt hlowerUpper]
    using hsafe

/--
At an opponent node with two counters, both choices are safe when either resulting singleton lets
the owner catch up.
-/
private theorem can_avoid_loss_pair_other (owner : Player) (lower upper deficit : ℕ)
    (hlowerUpper : lower < upper) (hdeficitLower : deficit ≤ lower)
    (hupperSafe : upper - deficit ≤ lower) :
    CanAvoidLoss owner
      { remaining := {lower, upper}
        deficit
        toMove := owner.other } := by
  let position : GamePosition :=
    { remaining := {lower, upper}
      deficit
      toMove := owner.other }
  have hterminal : ¬position.IsTerminal := by
    simp [position, GamePosition.IsTerminal, ne_of_lt hlowerUpper]
    omega
  apply (can_avoid_loss_iff_forall_safe_moves owner position hterminal (other_ne_self owner)).2
  intro counter hcounter
  have hcases : counter = lower ∨ counter = upper := by
    simpa [position, GamePosition.LegalMove] using hcounter
  rcases hcases with hcounterEq | hcounterEq
  · subst counter
    have hsafe :=
      can_avoid_loss_singleton_owner_of_le owner upper (lower - deficit) (by omega)
    simpa [position, GamePosition.afterPick, Position.afterPick,
      not_lt_of_ge hdeficitLower, ne_of_lt hlowerUpper, other_other] using hsafe
  · subst counter
    have hsafe :=
      can_avoid_loss_singleton_owner_of_le owner lower (upper - deficit) hupperSafe
    have herase : ({lower, upper} : Finset ℕ).erase upper = {lower} := by
      ext counter
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl | rfl⟩
        · rfl
        · contradiction
      · rintro rfl
        exact ⟨by omega, Or.inl rfl⟩
    simpa [position, GamePosition.afterPick, Position.afterPick,
      not_lt_of_ge (by omega : deficit ≤ upper), herase, other_other] using hsafe

/--
An explicit parametric family of safe three-counter Catch-Up positions.

Let the remaining counters be $x < a < b$, let the opponent be next to move, and let the opponent's
deficit be $d$ with $0 < d \leq a$.  Write $r = b-a$.  The owner can avoid losing if either
$x+r \leq d$, or if all four inequalities
$d \leq x \leq d+r$, $r \leq x+d$, and $x+d < b$ hold.
-/
theorem can_avoid_loss_three_counters (owner : Player) (x lower upper deficit : ℕ)
    (hxLower : x < lower) (hlowerUpper : lower < upper)
    (hdeficitPos : 0 < deficit) (hdeficitLower : deficit ≤ lower)
    (hregion :
      x + (upper - lower) ≤ deficit ∨
        (deficit ≤ x ∧ x ≤ deficit + (upper - lower) ∧
          upper - lower ≤ x + deficit ∧ x + deficit < upper)) :
    CanAvoidLoss owner
      { remaining := {x, lower, upper}
        deficit
        toMove := owner.other } := by
  let position : GamePosition :=
    { remaining := {x, lower, upper}
      deficit
      toMove := owner.other }
  have hxUpper : x < upper := by omega
  have heraseX : ({x, lower, upper} : Finset ℕ).erase x = {lower, upper} := by
    ext counter
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    omega
  have heraseLower : ({x, lower, upper} : Finset ℕ).erase lower = {x, upper} := by
    ext counter
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    omega
  have heraseUpper : ({x, lower, upper} : Finset ℕ).erase upper = {x, lower} := by
    ext counter
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hterminal : ¬position.IsTerminal := by
    simp [position, GamePosition.IsTerminal, ne_of_lt hxLower, ne_of_lt hxUpper,
      ne_of_lt hlowerUpper]
    omega
  apply (can_avoid_loss_iff_forall_safe_moves owner position hterminal
    (other_ne_self owner)).2
  intro counter hcounter
  have hcounterCases : counter = x ∨ counter = lower ∨ counter = upper := by
    simpa [position, GamePosition.LegalMove] using hcounter
  rcases hregion with hleft | hright
  · rcases hcounterCases with hcounterEq | hcounterEq | hcounterEq
    · subst counter
      have hxDeficit : x < deficit := by omega
      have hsafe := can_avoid_loss_pair_other owner lower upper (deficit - x)
        hlowerUpper (by omega) (by omega)
      simpa [position, GamePosition.afterPick, Position.afterPick, hxDeficit, heraseX] using hsafe
    · subst counter
      have hsafe := can_avoid_loss_pair_owner_take_upper owner x upper (lower - deficit)
        hxUpper (by omega) (by omega)
      simpa [position, GamePosition.afterPick, Position.afterPick,
        not_lt_of_ge hdeficitLower, heraseLower, other_other] using hsafe
    · subst counter
      have hsafe := can_avoid_loss_pair_owner_take_upper owner x lower (upper - deficit)
        hxLower (by omega) (by omega)
      simpa [position, GamePosition.afterPick, Position.afterPick,
        not_lt_of_ge (by omega : deficit ≤ upper), heraseUpper, other_other] using hsafe
  · rcases hright with ⟨hdeficitX, hxBound, hgapBound, hxDeficitUpper⟩
    rcases hcounterCases with hcounterEq | hcounterEq | hcounterEq
    · subst counter
      have hsafe := can_avoid_loss_pair_owner_take_upper owner lower upper (x - deficit)
        hlowerUpper (by omega) (by omega)
      simpa [position, GamePosition.afterPick, Position.afterPick,
        not_lt_of_ge hdeficitX, heraseX, other_other] using hsafe
    · subst counter
      have hsafe := can_avoid_loss_pair_owner_take_upper owner x upper (lower - deficit)
        hxUpper (by omega) (by omega)
      simpa [position, GamePosition.afterPick, Position.afterPick,
        not_lt_of_ge hdeficitLower, heraseLower, other_other] using hsafe
    · subst counter
      have hsafe := can_avoid_loss_pair_owner_take_both owner x lower (upper - deficit)
        hxLower (by omega) (by omega)
      simpa [position, GamePosition.afterPick, Position.afterPick,
        not_lt_of_ge (by omega : deficit ≤ upper), heraseUpper, other_other] using hsafe

end CatchUpSearch.ThreeCounterSafety
