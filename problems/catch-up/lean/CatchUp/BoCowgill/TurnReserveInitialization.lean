/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/TurnReserveInitialization.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic

/-!
# Initialization obstruction for prepaid turn reserves

A pairing reserve with total gap budget D and an unpaired pool of total W requires
D + W ≤ L and L + D + W ≤ x for every paired counter x, where L is the waiting
protected player's lead. Each unequal integer pair costs at least one unit of D.

This module classifies the weaker numerical envelope immediately after an opening
from the interval {3,...,N} at deficit one. For N ≥ 7, it is feasible exactly at
N = 7 with opening three. The envelope is only a necessary condition for this
specific strategy certificate; it is not an outcome characterization.

*Reference:* The completed-turn semantics in `catch_up.CompletedTurn`.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.TurnReserve

open scoped BigOperators

/-- A necessary numerical envelope for a prepaid pairing reserve, not a safety predicate. -/
def BudgetEnvelope (S : Finset ℕ) (L : ℕ) : Prop :=
  ∃ B : Finset ℕ, B ⊆ S ∧ ∃ D : ℕ,
    (S \ B).card ≤ 2 * D ∧
    D + B.sum (fun x ↦ x) ≤ L ∧
    ∀ x ∈ S \ B, L + D + B.sum (fun y ↦ y) ≤ x

private theorem nonempty_reserve_rigidity (N a D : ℕ) (B : Finset ℕ)
    (ha : a ∈ Finset.Icc 3 N)
    (hB : B ⊆ (Finset.Icc 3 N).erase a)
    (hP : ((Finset.Icc 3 N).erase a \ B).Nonempty)
    (hcard : ((Finset.Icc 3 N).erase a \ B).card ≤ 2 * D)
    (hupper : ∀ x ∈ (Finset.Icc 3 N).erase a \ B,
      a - 1 + D + B.sum (fun y ↦ y) ≤ x) :
    a = 3 ∧ B = ∅ ∧ N ≤ 7 := by
  let P := (Finset.Icc 3 N).erase a \ B
  let m := P.min' hP
  have hm : m ∈ P := P.min'_mem hP
  have hmS := (Finset.mem_sdiff.mp hm).1
  have ha3 := (Finset.mem_Icc.mp ha).1
  have hmBounds := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hmS)
  have hmNe := (Finset.mem_erase.mp hmS).1
  have hD : 1 ≤ D := by have := Finset.card_pos.mpr hP; omega
  have hbudget := hupper m hm
  have ham : a + B.sum (fun y ↦ y) ≤ m := by omega
  have hma : a + 1 ≤ m := by omega
  have hlowB : ∀ x ∈ (Finset.Icc 3 N).erase a, x < m → x ∈ B := by
    intro x hx hxm
    by_contra hxB
    have hxP : x ∈ P := Finset.mem_sdiff.mpr ⟨hx, hxB⟩
    have hmin : m ≤ x := P.min'_le x hxP
    omega
  have hmaEq : m = a + 1 := by
    by_contra hne
    have hm2 : a + 2 ≤ m := by omega
    have hprev : m - 1 ∈ (Finset.Icc 3 N).erase a :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    have hprevB := hlowB (m - 1) hprev (by omega)
    have hprevSum : m - 1 ≤ B.sum (fun x ↦ x) :=
      Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hprevB
    omega
  have haEq : a = 3 := by
    by_contra hne
    have hthree : 3 ∈ (Finset.Icc 3 N).erase a :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    have hthreeB := hlowB 3 hthree (by omega)
    have hthreeSum : 3 ≤ B.sum (fun x ↦ x) :=
      Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hthreeB
    omega
  have hBEq : B = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    have hx3 := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase (hB hx))).1
    have hxSum : x ≤ B.sum (fun y ↦ y) :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
    omega
  have hsumB : B.sum (fun x ↦ x) = 0 := by simp [hBEq]
  have hDle : D ≤ 2 := by omega
  have hcardS : ((Finset.Icc 3 N).erase a).card ≤ 2 * D := by
    simpa [hBEq] using hcard
  have hcardErase := Finset.card_erase_add_one ha
  have hcardIcc : (Finset.Icc 3 N).card = N + 1 - 3 := Nat.card_Icc 3 N
  exact ⟨haEq, hBEq, by omega⟩

private theorem opening_mass (N a : ℕ) (hN : 7 ≤ N)
    (ha : a ∈ Finset.Icc 3 N) :
    a - 1 < ((Finset.Icc 3 N).erase a).sum (fun x ↦ x) := by
  have hsub : ({3, N - 1, N} : Finset ℕ) ⊆ Finset.Icc 3 N := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.mem_Icc]
    omega
  have hs := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x) hsub
  have hne3 : 3 ≠ N := by omega
  have hne31 : 3 ≠ N - 1 := by omega
  have hneN : N - 1 ≠ N := by omega
  have hs' : 3 + (N - 1) + N ≤ (Finset.Icc 3 N).sum (fun x ↦ x) := by
    simpa [hne3, hne31, hneN, Nat.add_assoc] using hs
  have he := Finset.sum_erase_add (Finset.Icc 3 N) (fun x ↦ x) ha
  have haN := (Finset.mem_Icc.mp ha).2
  try dsimp only at he
  omega

private theorem budget_envelope_initialization_rigidity (N a : ℕ)
    (hN : 7 ≤ N) (ha : a ∈ Finset.Icc 3 N)
    (h : BudgetEnvelope ((Finset.Icc 3 N).erase a) (a - 1)) :
    N = 7 ∧ a = 3 := by
  obtain ⟨B, hB, D, hcard, hlower, hupper⟩ := h
  have hP : ((Finset.Icc 3 N).erase a \ B).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    have hsub := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have hsum := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x) hsub
    have hmass := opening_mass N a hN ha
    try dsimp only at hsum
    omega
  obtain ⟨haEq, _, hNle⟩ := nonempty_reserve_rigidity N a D B ha hB hP hcard hupper
  exact ⟨by omega, haEq⟩

/-- For N ≥ 7, the prepaid reserve envelope after an interval opening is feasible
exactly at N = 7 with opening three. No parity or outcome hypothesis is required. -/
theorem budget_envelope_initialization_iff (N a : ℕ)
    (hN : 7 ≤ N) (ha : a ∈ Finset.Icc 3 N) :
    BudgetEnvelope ((Finset.Icc 3 N).erase a) (a - 1) ↔ N = 7 ∧ a = 3 := by
  constructor
  · exact budget_envelope_initialization_rigidity N a hN ha
  · rintro ⟨rfl, rfl⟩
    refine ⟨∅, by simp, 2, ?_, ?_, ?_⟩
    all_goals decide +kernel

end CatchUp.TurnReserve
