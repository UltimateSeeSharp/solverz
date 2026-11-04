/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CompletedTurnReflection.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.CompletedTurn

/-!
# Deficit–Excess Reflection for Completed Catch-Up Turns

This module characterizes when a completed turn can be replayed after reflecting its old deficit
through the sum of its chosen counters. It isolates the singleton boundary at zero reflected
deficit and gives a clean high-maximum criterion when the old deficit counter is unavailable.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- At zero deficit, the current player's completed turn consists of exactly one counter. -/
theorem exists_turn_set_deficit_zero_iff_singleton
    (before : GamePosition) (chosen : Finset ℕ)
    (hzero : before.deficit = 0) :
    (∃ final, TurnSet before chosen final) ↔
      ∃ final ∈ before.remaining, chosen = {final} := by
  constructor
  · rintro ⟨final, turn⟩
    refine ⟨final, turn.chosen_subset turn.final_mem, ?_⟩
    rcases turn.preparation_below with hsingleton | hbelow
    · exact hsingleton
    · rw [hzero] at hbelow
      omega
  · rintro ⟨final, hfinal, rfl⟩
    refine ⟨final, ?_⟩
    refine ⟨by simp, ?_, ?_, Or.inl rfl⟩
    · simpa using hfinal
    · simp [hzero]

/-- At positive reflected excess, replaying the same chosen set is legal exactly when the old
deficit is strictly below the chosen maximum. -/
theorem exists_turn_set_at_positive_excess_iff_deficit_lt_max
    (before : GamePosition) (chosen : Finset ℕ)
    (hchosen : chosen.Nonempty)
    (hsubset : chosen ⊆ before.remaining)
    (hcatches : before.deficit ≤ chosen.sum (fun x ↦ x))
    (hexcess : 0 < chosen.sum (fun x ↦ x) - before.deficit) :
    (∃ final,
        TurnSet
          { before with deficit := chosen.sum (fun x ↦ x) - before.deficit }
          chosen final) ↔
      before.deficit < chosen.max' hchosen := by
  rw [exists_turn_set_iff_sum_lt_deficit_add_max _ _ hexcess]
  constructor
  · rintro ⟨hchosen', _, _, hbelow⟩
    try simp only at hbelow
    omega
  · intro hd
    refine ⟨hchosen, hsubset, ?_, ?_⟩
    · change chosen.sum (fun x ↦ x) - before.deficit ≤ chosen.sum (fun x ↦ x)
      omega
    · change chosen.sum (fun x ↦ x) <
        (chosen.sum (fun x ↦ x) - before.deficit) + chosen.max' hchosen
      omega

/-- Reflecting the deficit through the chosen-set sum twice returns the original deficit. -/
theorem completed_turn_deficit_reflection_involutive
    (before : GamePosition) (chosen : Finset ℕ)
    (hcatches : before.deficit ≤ chosen.sum (fun x ↦ x)) :
    chosen.sum (fun x ↦ x) -
        (chosen.sum (fun x ↦ x) - before.deficit) = before.deficit := by
  omega

/-- If the same positive-excess turn cannot be replayed after reflecting its deficit, and the old
deficit counter is unavailable, the entire chosen set lies strictly below the old deficit. -/
theorem chosen_max_lt_deficit_of_no_positive_excess_reflection
    (before : GamePosition) (chosen : Finset ℕ)
    (hchosen : chosen.Nonempty)
    (hsubset : chosen ⊆ before.remaining)
    (hcatches : before.deficit ≤ chosen.sum (fun x ↦ x))
    (hexcess : 0 < chosen.sum (fun x ↦ x) - before.deficit)
    (hmissing : before.deficit ∉ before.remaining)
    (honeway : ¬ ∃ final,
      TurnSet
        { before with deficit := chosen.sum (fun x ↦ x) - before.deficit }
        chosen final) :
    chosen.max' hchosen < before.deficit := by
  have hnotlt : ¬ before.deficit < chosen.max' hchosen := by
    intro hlt
    apply honeway
    exact (exists_turn_set_at_positive_excess_iff_deficit_lt_max
      before chosen hchosen hsubset hcatches hexcess).2 hlt
  have hmaxmem : chosen.max' hchosen ∈ before.remaining := by
    exact hsubset (Finset.max'_mem chosen hchosen)
  have hne : chosen.max' hchosen ≠ before.deficit := by
    intro heq
    apply hmissing
    simpa [heq] using hmaxmem
  omega

/-- When the old deficit counter is unavailable, replaying a chosen set at its reflected deficit
is legal exactly on the high-maximum side. This combines the positive-excess reflection with the
zero-excess singleton boundary. -/
theorem exists_turn_set_at_excess_iff_deficit_lt_max_of_missing
    (before : GamePosition) (chosen : Finset ℕ)
    (hchosen : chosen.Nonempty)
    (hsubset : chosen ⊆ before.remaining)
    (hcatches : before.deficit ≤ chosen.sum (fun x ↦ x))
    (hmissing : before.deficit ∉ before.remaining) :
    (∃ final,
        TurnSet
          { before with deficit := chosen.sum (fun x ↦ x) - before.deficit }
          chosen final) ↔
      before.deficit < chosen.max' hchosen := by
  constructor
  · intro hreflected
    by_cases hzero : chosen.sum (fun x ↦ x) - before.deficit = 0
    · let reflected : GamePosition :=
        { before with deficit := chosen.sum (fun x ↦ x) - before.deficit }
      have hreflectedZero : reflected.deficit = 0 := by
        simpa [reflected] using hzero
      obtain ⟨final, hfinal, hsingleton⟩ :=
        (exists_turn_set_deficit_zero_iff_singleton reflected chosen hreflectedZero).1
          hreflected
      have hsumSingleton : chosen.sum (fun x ↦ x) = final := by
        rw [hsingleton]
        simp
      have hfinalEq : final = before.deficit := by omega
      exfalso
      apply hmissing
      rw [← hfinalEq]
      simpa [reflected] using hfinal
    · have hexcess : 0 < chosen.sum (fun x ↦ x) - before.deficit :=
        Nat.pos_of_ne_zero hzero
      exact (exists_turn_set_at_positive_excess_iff_deficit_lt_max
        before chosen hchosen hsubset hcatches hexcess).1 hreflected
  · intro hd
    have hmaxLeSum : chosen.max' hchosen ≤ chosen.sum (fun x ↦ x) := by
      exact Finset.single_le_sum (fun x _ ↦ Nat.zero_le x)
        (Finset.max'_mem chosen hchosen)
    have hexcess : 0 < chosen.sum (fun x ↦ x) - before.deficit := by omega
    exact (exists_turn_set_at_positive_excess_iff_deficit_lt_max
      before chosen hchosen hsubset hcatches hexcess).2 hd

end CatchUp
