/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ConsecutiveGuardBoundary.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.ConsecutiveGuardDescent
public import CatchUp.NearMaximumDefense

/-!
# A near-maximum defense excludes the top six large first picks

A hypothetical winning pick on `{3,4} ∪ Icc 9 N` supplies a residual losing
opening at least four labels higher. Continuing with counter three exposes a
position covered by `NearMaximumDefense` if fewer than six labels remain above
the original pick. This gives an unbounded interval restriction, without parity.

No residual winning opening is promoted to the original support, and the value
of the full position is not determined here.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.ConsecutiveGuardBoundary
open ConsecutiveGuardDescent

/-- A winning large first counter must leave at least six larger labels. -/
theorem winning_pick_bound (N q : ℕ) (hq : 14 ≤ q) (hqN : q ≤ N)
    (hwin : (⟨support N,1⟩ : Position).moveOutcome q = .win) :
    q+6 ≤ N := by
  by_contra hbound
  have hl : (⟨(support N).erase q,q-1⟩ : Position).value = .loss := by
    simp only [Position.moveOutcome,Position.afterPick,show ¬q<1 by omega,ite_false] at hwin
    cases hv : (⟨(support N).erase q,q-1⟩ : Position).value <;> simp_all [Outcome.neg]
  obtain ⟨w,hw,hgap,hs⟩ := ConsecutiveGuardDescent.losing_child_reentry N q hq hqN hl
  have hwN : w ≤ N := by
    simp only [ConsecutiveGuardDescent.residual,support,mem_sdiff,mem_erase,mem_union,mem_insert,mem_singleton,mem_Icc] at hw
    omega
  let C := (ConsecutiveGuardDescent.residual N q).erase w
  have hC (x : ℕ) : x ∈ C ↔ x ≠ w ∧ (x ≠ q ∧ (x=3 ∨ x=4 ∨ 9 ≤ x ∧ x ≤ N)) ∧ x ≠ q-1 := by
    simp [C,ConsecutiveGuardDescent.residual,support]
  have h3 : 3 ∈ C := by simp [hC]; omega
  have hd := PairEntranceShadow.loss_after_subsum C {3} w
    (singleton_subset_iff.mpr h3) (by simp; omega) (by simpa [C,afterOpening] using hs)
  have hn : (⟨C \ {3},w-3⟩ : Position).value ≠ .loss := by
    apply NearMaximumDefense.value_ne_loss (C \ {3}) 4 (w-3) (by omega)
    all_goals (simp [hC]; omega)
  exact hn (by simpa using hd)

/-- Every available tail label within five of the maximum is nonwinning. -/
theorem top_six_pick_nonwin (N q : ℕ) (hq : 14 ≤ q) (hqN : q ≤ N)
    (htop : N < q+6) :
    (⟨support N,1⟩ : Position).moveOutcome q ≠ .win := by
  intro hwin
  exact (Nat.not_le_of_gt htop) (winning_pick_bound N q hq hqN hwin)

end CatchUp.ConsecutiveGuardBoundary

