/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Search.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Executable

/-!
# The high-level Catch-Up counterexample search

A state is the next integer to examine. `next` either halts or advances by one. `runFor` is a
bounded observation of this transition system, not a total definition of its unbounded search.
One transition contains a total finite game evaluation. No resource timeout is a game outcome.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.Search

/-- The literal universally quantified reference proposition, including `N = 0`. -/
def Conjecture : Prop :=
  ∀ N : ℕ, Even (N * (N + 1) / 2) → value (Finset.Icc 1 N) = .draw

/-- An exact executable test for a counterexample. -/
def isCounterexample (N : ℕ) : Bool :=
  decide (Even (N * (N + 1) / 2)) &&
    decide (evalInitial (Finset.Icc 1 N) ≠ .draw)

/-- The test refers to the reference minimax value, not to one policy or one play. -/
theorem is_counterexample_iff (N : ℕ) :
    isCounterexample N = true ↔
      Even (N * (N + 1) / 2) ∧ value (Finset.Icc 1 N) ≠ .draw := by
  simp only [isCounterexample, Bool.and_eq_true, decide_eq_true_eq, eval_initial_eq_value]

/-- One outer search transition, starting at `1`. -/
def next (N : ℕ) : Option ℕ :=
  if isCounterexample N then none else some (N + 1)

/-- A finite observation of the possibly infinite search. `none` is absorbing. -/
def runFor (start : ℕ) : ℕ → Option ℕ
  | 0 => some start
  | steps + 1 =>
      match next start with
      | none => none
      | some successor => runFor successor steps

/-- A single transition on optional states, with the halted state absorbing. -/
def tick (state : Option ℕ) : Option ℕ := state.bind next

/-- The halted state remains halted under any number of transitions. -/
theorem tick_iterate_none (steps : ℕ) : tick^[steps] none = none :=
  Function.iterate_fixed rfl steps

/-- The bounded observation is actual iteration of the partial transition, in both directions. -/
theorem run_for_eq_iterate (start steps : ℕ) :
    runFor start steps = tick^[steps] (some start) := by
  induction steps generalizing start with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      cases hnext : next start with
      | none => simp [runFor, tick, hnext, tick_iterate_none]
      | some successor => simpa [runFor, tick, hnext] using ih successor

/-- Halting means that some finite number of actual transitions reaches `none`. -/
def Halts : Prop := ∃ steps, runFor 1 steps = none

/-- Every finite observation either halts or reaches exactly the expected next integer. -/
theorem run_for_shape (start steps : ℕ) :
    runFor start steps = none ∨ runFor start steps = some (start + steps) := by
  induction steps generalizing start with
  | zero => exact Or.inr (by simp [runFor])
  | succ steps ih =>
      by_cases hbad : isCounterexample start = true
      · left
        simp [runFor, next, hbad]
      · simpa [runFor, next, hbad, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (start + 1)

/-- A bounded run halts precisely when one of the examined integers is a counterexample. -/
theorem run_for_eq_none_iff (start steps : ℕ) :
    runFor start steps = none ↔
      ∃ offset < steps, isCounterexample (start + offset) = true := by
  induction steps generalizing start with
  | zero => simp [runFor]
  | succ steps ih =>
      by_cases hbad : isCounterexample start = true
      · simp only [runFor, next, hbad, ↓reduceIte]
        exact ⟨fun _ ↦ ⟨0, by omega, by simpa using hbad⟩, fun _ ↦ True.intro⟩
      · have hgood : isCounterexample start = false := Bool.eq_false_iff.mpr hbad
        simp only [runFor, next, hgood, Bool.false_eq_true, ↓reduceIte]
        rw [ih]
        constructor
        · rintro ⟨offset, hoffset, hcounter⟩
          refine ⟨offset + 1, by omega, ?_⟩
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcounter
        · rintro ⟨offset, hoffset, hcounter⟩
          have hpos : 0 < offset := by
            by_contra h
            have hz : offset = 0 := by omega
            simp [hz, hgood] at hcounter
          refine ⟨offset - 1, by omega, ?_⟩
          have heq : start + 1 + (offset - 1) = start + offset := by omega
          simpa [heq] using hcounter

/-- Each integer is reached unless a smaller counterexample has already caused halting. -/
theorem reaches_or_earlier_counterexample (N : ℕ) (hN : 1 ≤ N) :
    runFor 1 (N - 1) = some N ∨
      ∃ earlier, 1 ≤ earlier ∧ earlier < N ∧ isCounterexample earlier = true := by
  rcases run_for_shape 1 (N - 1) with hhalt | hreach
  · right
    obtain ⟨offset, hoffset, hbad⟩ := (run_for_eq_none_iff 1 (N - 1)).mp hhalt
    exact ⟨1 + offset, by omega, by omega, hbad⟩
  · left
    simpa [show 1 + (N - 1) = N by omega] using hreach

/-- The search halts exactly when an eligible non-drawing interval exists. -/
theorem halts_iff_exists_counterexample :
    Halts ↔ ∃ N, 1 ≤ N ∧ Even (N * (N + 1) / 2) ∧
      value (Finset.Icc 1 N) ≠ .draw := by
  constructor
  · rintro ⟨steps, hsteps⟩
    obtain ⟨offset, _, hbad⟩ := (run_for_eq_none_iff 1 steps).mp hsteps
    exact ⟨1 + offset, by omega, (is_counterexample_iff _).mp hbad⟩
  · rintro ⟨N, hN, heven, hvalue⟩
    refine ⟨N, (run_for_eq_none_iff 1 N).mpr ?_⟩
    refine ⟨N - 1, by omega, ?_⟩
    have heq : 1 + (N - 1) = N := by omega
    rw [heq, is_counterexample_iff]
    exact ⟨heven, hvalue⟩

/-- The high-level counterexample search halts iff the reference conjecture is false. -/
theorem halts_iff_not_conjecture : Halts ↔ ¬ Conjecture := by
  rw [halts_iff_exists_counterexample]
  constructor
  · rintro ⟨N, _, heven, hvalue⟩ hconjecture
    exact hvalue (hconjecture N heven)
  · intro hnot
    classical
    unfold Conjecture at hnot
    push Not at hnot
    obtain ⟨N, heven, hvalue⟩ := hnot
    have hN : 1 ≤ N := by
      by_contra h
      have hz : N = 0 := by omega
      subst N
      exact hvalue value_Icc_zero
    exact ⟨N, hN, heven, hvalue⟩

/-- The halting predicate matches Cryptids' `CollatzHalts` interface literally. -/
theorem iterate_halts_iff_not_conjecture :
    (∃ steps : ℕ, ((Option.bind · next)^[steps] (some 1)).isNone) ↔ ¬ Conjecture := by
  rw [← halts_iff_not_conjecture]
  change (∃ steps : ℕ, (tick^[steps] (some 1)).isNone) ↔ Halts
  simp only [Halts, run_for_eq_iterate, Option.isNone_iff_eq_none]

end CatchUp.Search
