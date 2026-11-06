/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/LowerRayEndpoints.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.DeficitWinningBound

/-!
# Upper endpoints of the lower pair-deletion ray

An exact two-counter strategy-stealing argument proves nonloss at the penultimate member of the
lower pair-deletion ray. Together with the maximum-deficit result, this settles the top two members
without a parity assumption.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

private theorem move_outcome_eq_loss_of_value_eq_loss
    (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit)
    (x : ℕ) (hx : x ∈ position.remaining)
    (hloss : position.value = .loss) :
    position.moveOutcome x = .loss := by
  by_contra hmove
  have hbestNe :
      Outcome.best
          (position.remaining.attach.toList.map fun move ↦
            position.moveOutcome move.1) ≠ .loss := by
    rw [Outcome.best_ne_loss_iff]
    refine ⟨position.moveOutcome x, ?_, hmove⟩
    apply List.mem_map.mpr
    exact ⟨⟨x, hx⟩, by simp, rfl⟩
  rw [Position.value_eq_best_move_outcome position hremaining hcatch] at hloss
  exact hbestNe hloss

/-- If two available counters exactly fill the deficit and the second dominates the residual,
then the player to move cannot lose. -/
theorem Position.value_ne_loss_of_exact_pair_dominates
    (remaining : Finset ℕ) (deficit a c : ℕ)
    (ha : a ∈ remaining) (hc : c ∈ remaining) (hac : a ≠ c)
    (hcpos : 0 < c) (hdeficit : deficit = a + c)
    (hdominates : ∀ y ∈ (remaining.erase a).erase c, y < c) :
    Position.value ⟨remaining, deficit⟩ ≠ .loss := by
  intro hloss
  let position : Position := ⟨remaining, deficit⟩
  have hremaining : position.remaining ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨a, ha⟩
  have hcAfterA : c ∈ remaining.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hac, hc⟩
  have hsumC : c ≤ (remaining.erase a).sum (fun x ↦ x) :=
    Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hcAfterA
  have hsumEraseA : (remaining.erase a).sum (fun x ↦ x) + a =
      remaining.sum (fun x ↦ x) :=
    Finset.sum_erase_add remaining (fun x ↦ x) ha
  have hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit := by
    simp only [position]
    rw [hdeficit]
    omega
  have hmoveA : position.moveOutcome a = .loss :=
    move_outcome_eq_loss_of_value_eq_loss position hremaining hcatch a ha hloss
  have haContinue : a < deficit := by
    rw [hdeficit]
    omega
  let afterA := position.afterPick a
  have hafterALoss : afterA.value = .loss := by
    simpa [afterA, Position.moveOutcome, position, haContinue] using hmoveA
  have hafterADeficit : afterA.deficit = c := by
    change (if a < deficit then deficit - a else a - deficit) = c
    rw [ite_eq_left haContinue, hdeficit]
    omega
  have hcAfterARemaining : c ∈ afterA.remaining := by
    simpa [afterA, position, Position.afterPick] using hcAfterA
  have hmaxAfterA : ∀ x ∈ afterA.remaining, x ≤ afterA.deficit := by
    intro x hx
    rw [hafterADeficit]
    by_cases hxc : x = c
    · omega
    · have hlt : x < c := hdominates x (by
        exact Finset.mem_erase.mpr
          ⟨hxc, by simpa [afterA, position, Position.afterPick] using hx⟩)
      exact hlt.le
  have hdeficitAfterA : afterA.deficit ∈ afterA.remaining := by
    rw [hafterADeficit]
    exact hcAfterARemaining
  exact (Position.value_ne_loss_of_deficit_is_max
    afterA.remaining afterA.deficit hdeficitAfterA hmaxAfterA) hafterALoss

/-- A consecutive tail is nonlosing when its deficit is three above its maximum counter. -/
theorem interval_tail_value_ne_loss_of_deficit_eq_top_add_three
    (m : ℕ) (hm : 4 ≤ m) :
    Position.value ⟨Finset.Icc 2 m, m + 3⟩ ≠ .loss := by
  apply Position.value_ne_loss_of_exact_pair_dominates
      (Finset.Icc 2 m) (m + 3) 3 m
  · simp
    omega
  · simp
    omega
  · omega
  · omega
  · omega
  · intro y hy
    simp only [Finset.mem_erase, Finset.mem_Icc] at hy
    omega

/-- The member immediately below the top of the lower pair-deletion ray is always nonlosing. -/
theorem pair_deletion_position_penultimate_value_ne_loss
    (N : ℕ) (hN : 7 ≤ N) :
    (pairDeletionPosition N 1 (N - 1)).value ≠ .loss := by
  intro hloss
  let remaining := ((Finset.Icc 1 N).erase 1).erase (N - 1)
  have hdeficit : N - 2 ∈ remaining := by
    simp [remaining]
    omega
  obtain ⟨_, y, hyResidual, hyLoss, hyLarger, _⟩ :=
    loss_with_available_deficit_forces_large_unique_winning_opening
      remaining (N - 2) hdeficit
        (by simpa [remaining, pairDeletionPosition, Nat.sub_sub] using hloss)
  have hyEq : y = N := by
    simp only [remaining, Finset.mem_erase, Finset.mem_Icc] at hyResidual
    omega
  subst y
  let residual := remaining.erase (N - 2)
  have hendpoint : afterOpening residual N =
      (⟨Finset.Icc 2 (N - 3), N⟩ : Position) := by
    simp only [afterOpening]
    rw [Position.mk.injEq]
    constructor
    · ext x
      simp [residual, remaining]
      omega
    · rfl
  rw [hendpoint] at hyLoss
  have htail := interval_tail_value_ne_loss_of_deficit_eq_top_add_three (N - 3) (by omega)
  have htop : N - 3 + 3 = N := by omega
  rw [htop] at htail
  exact htail hyLoss

end CatchUp
