/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseTerminalNonloss.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DenseTerminalReduction
public import CatchUp.BoCowgill.Executable
public import CatchUp.BoCowgill.ExactSumLossObstruction

/-!
# Nonloss in the actual terminal subsum-gap branch

The uniform arithmetic cutoff reduces this branch to eight small successor positions.
The finite classification and successor values are checked in Lean's kernel.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseTerminalNonloss

open CatchUp (Position.loss_after_continuing_pick)

/-- The eight successors in the bounded arithmetic terminal-branch classification. -/
def successors : Finset Position :=
  {⟨{2, 3}, 1⟩, ⟨{2, 5}, 1⟩, ⟨{2, 3, 4}, 1⟩, ⟨{1, 3, 4}, 2⟩,
    ⟨{1, 3, 6}, 2⟩, ⟨{2, 4, 5}, 1⟩, ⟨{1, 3, 4, 6}, 2⟩, ⟨{2, 3, 4, 6}, 1⟩}

/-- Only finite arithmetic conditions are used by the bounded classifier. -/
def finiteArithmeticCase (N d w : ℕ) (S : Finset ℕ) : Prop :=
  2 * (Icc 1 N \ S).card + 1 ≤ d ∧ Even (S.sum (fun x ↦ x) + d) ∧
    w < d ∧ 1 ≤ d - w ∧ d - w < (Icc 1 N \ S).card ∧
    (∀ A ∈ S.powerset, A.sum (fun x ↦ x) ≠ d - w) ∧
    ∃ B ∈ S.powerset, w ∉ B ∧ B.sum (fun x ↦ x) = d ∧
      ((S \ B).erase w).sum (fun x ↦ x) < w

instance (N d w : ℕ) (S : Finset ℕ) : Decidable (finiteArithmeticCase N d w S) := by
  unfold finiteArithmeticCase
  infer_instance

/-- Exhaustive arithmetic classification for N at most nine, independent of game evaluation. -/
theorem bounded_classification :
    ∀ N ∈ Finset.range 10, ∀ S ∈ (Icc 1 N).powerset,
      ∀ d ∈ Icc 1 N, ∀ w ∈ S, finiteArithmeticCase N d w S →
        (⟨S.erase w, d - w⟩ : Position) ∈ successors := by
  decide +kernel

/-- Exact kernel evaluations of the eight classified successors. -/
theorem successor_values :
    (⟨{2, 3}, 1⟩ : Position).value = .draw ∧
    (⟨{2, 5}, 1⟩ : Position).value = .win ∧
    (⟨{2, 3, 4}, 1⟩ : Position).value = .draw ∧
    (⟨{1, 3, 4}, 2⟩ : Position).value = .draw ∧
    (⟨{1, 3, 6}, 2⟩ : Position).value = .win ∧
    (⟨{2, 4, 5}, 1⟩ : Position).value = .draw ∧
    (⟨{1, 3, 4, 6}, 2⟩ : Position).value = .draw ∧
    (⟨{2, 3, 4, 6}, 1⟩ : Position).value = .win := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [← Position.eval_eq_value]
  all_goals decide +kernel

/-- Every successor in the arithmetic classification is nonlosing. -/
theorem successors_nonloss (p : Position) (hp : p ∈ successors) : p.value ≠ .loss := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := successor_values
  simp only [successors, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- The actual terminal subsum-gap branch has a nonlosing continuing successor for every N. -/
theorem terminal_gap_successor_nonloss
    (N d w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (heven : Even (S.sum (fun x ↦ x) + d))
    (hB : B ⊆ S) (hsumB : B.sum (fun x ↦ x) = d)
    (hw : w ∈ S \ B) (hwd : w < d) (htsmall : d - w < (Icc 1 N \ S).card)
    (hgap : ∀ A : Finset ℕ, A ⊆ S → A.sum (fun x ↦ x) ≠ d - w)
    (hterminal : ((S \ B).erase w).sum (fun x ↦ x) < w) :
    (⟨S.erase w, d - w⟩ : Position).value ≠ .loss := by
  have htmissing : d - w ∉ S := by
    intro ht
    exact hgap {d - w} (by simpa using ht) (by simp)
  have hN := DenseTerminalReduction.terminal_branch_bound N d w S B hS hlarge hdN
    heven hB hsumB hw hwd htmissing hterminal
  have hcase : finiteArithmeticCase N d w S := by
    refine ⟨hlarge, heven, hwd, by omega, htsmall, ?_, B,
      mem_powerset.mpr hB, (mem_sdiff.mp hw).2, hsumB, hterminal⟩
    intro A hA
    exact hgap A (mem_powerset.mp hA)
  apply successors_nonloss
  exact bounded_classification N (Finset.mem_range.mpr (by omega)) S
    (mem_powerset.mpr hS) d (mem_Icc.mpr ⟨by omega, hdN⟩) w (mem_sdiff.mp hw).1 hcase

/-- The same terminal subsum-gap hypotheses also rule out a losing parent state. -/
theorem terminal_gap_parent_nonloss
    (N d w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (heven : Even (S.sum (fun x ↦ x) + d))
    (hB : B ⊆ S) (hsumB : B.sum (fun x ↦ x) = d)
    (hw : w ∈ S \ B) (hwd : w < d) (htsmall : d - w < (Icc 1 N \ S).card)
    (hgap : ∀ A : Finset ℕ, A ⊆ S → A.sum (fun x ↦ x) ≠ d - w)
    (hterminal : ((S \ B).erase w).sum (fun x ↦ x) < w) :
    (⟨S, d⟩ : Position).value ≠ .loss := by
  intro hloss
  have hchild := terminal_gap_successor_nonloss N d w S B hS hlarge hdN heven hB hsumB
    hw hwd htsmall hgap hterminal
  have hcatch : ¬ S.sum (fun x ↦ x) < d := by
    have hs := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x) hB
    try simp only at hs
    rw [hsumB] at hs
    omega
  have hl := Position.loss_after_continuing_pick (⟨S, d⟩ : Position)
    (mem_sdiff.mp hw).1 hcatch hwd hloss
  exact hchild (by simpa only [Position.afterPick, hwd, ite_true] using hl)

end CatchUp.DenseTerminalNonloss
