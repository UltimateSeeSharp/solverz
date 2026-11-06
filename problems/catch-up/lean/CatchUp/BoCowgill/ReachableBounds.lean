/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ReachableBounds.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Reference

/-!
# Bounds for Reachable Catch-Up Positions

This module proves that every absolute position reachable from an interval-game opening retains
only counters from the original interval and has normalized deficit at most the largest counter.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- Picking a counter bounded by $N$ preserves the same deficit bound. -/
theorem Position.deficit_after_pick_le
    (position : Position) (N x : ℕ)
    (hdeficit : position.deficit ≤ N) (hx : x ≤ N) :
    (position.afterPick x).deficit ≤ N := by
  simp only [Position.afterPick]
  split <;> omega

/-- Every counter remaining in a reachable interval position belongs to the original interval. -/
theorem ReachableFromOpening.remaining_subset_Icc
    {N opening : ℕ} {position : GamePosition}
    (hreachable : ReachableFromOpening N opening position) :
    position.remaining ⊆ Finset.Icc 1 N := by
  rcases hreachable with ⟨hopening, hsteps⟩
  induction hsteps with
  | refl =>
      simpa [GamePosition.afterOpening, CatchUp.afterOpening] using
        (Finset.erase_subset (s := Finset.Icc 1 N) opening)
  | tail hsteps hstep ih =>
      rcases hstep with ⟨_, x, hx, rfl⟩
      intro counter hcounter
      apply ih
      exact Finset.mem_of_mem_erase hcounter

/-- The normalized deficit of every reachable interval position is at most $N$. -/
theorem ReachableFromOpening.deficit_le
    {N opening : ℕ} {position : GamePosition}
    (hreachable : ReachableFromOpening N opening position) :
    position.deficit ≤ N := by
  rcases hreachable with ⟨hopening, hsteps⟩
  induction hsteps with
  | refl =>
      simpa [afterOpening] using (Finset.mem_Icc.mp hopening).2
  | tail hsteps hstep ih =>
      rcases hstep with ⟨_, x, hx, rfl⟩
      apply Position.deficit_after_pick_le
      · exact ih
      · have hxIcc : x ∈ Finset.Icc 1 N :=
          ReachableFromOpening.remaining_subset_Icc ⟨hopening, hsteps⟩ hx
        exact (Finset.mem_Icc.mp hxIcc).2

/-- A reachable interval position has at most $N$ remaining counters. -/
theorem ReachableFromOpening.remaining_card_le
    {N opening : ℕ} {position : GamePosition}
    (hreachable : ReachableFromOpening N opening position) :
    position.remaining.card ≤ N := by
  have hcard := Finset.card_le_card hreachable.remaining_subset_Icc
  simpa using hcard

end CatchUp
