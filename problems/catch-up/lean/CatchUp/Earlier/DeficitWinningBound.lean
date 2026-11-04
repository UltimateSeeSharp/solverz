/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/DeficitWinningBound.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.LowerRaySuccessor
public import CatchUp.WinningOpening

/-!
# Winning-opening bound forced by an available deficit

A losing normalized position whose exact deficit remains available forces a win at the tied
residual. The tied residual's globally unique winning opening must lie strictly above that deficit.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

private theorem position_value_tied_eq_value (S : Finset ℕ) :
    Position.value ⟨S, 0⟩ = value S := by
  rw [Position.value_eq_value_aux S 0 0 (by omega)]
  rw [value]
  rw [valueAux.eq_def, valueAux.eq_def]
  by_cases hS : S = ∅
  · simp [hS]
  · simp only [hS, Nat.zero_add, Nat.not_lt_zero, ite_false]
    congr 1

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

/-- If a losing position still contains its exact deficit, deleting that counter leaves a winning
tied root. Its globally unique winning opening is strictly larger than the deleted deficit. -/
theorem loss_with_available_deficit_forces_large_unique_winning_opening
    (remaining : Finset ℕ) (deficit : ℕ)
    (hdeficit : deficit ∈ remaining)
    (hloss : (⟨remaining, deficit⟩ : Position).value = .loss) :
    value (remaining.erase deficit) = .win ∧
      ∃ y, y ∈ remaining.erase deficit ∧
        (afterOpening (remaining.erase deficit) y).value = .loss ∧ deficit < y ∧
          ∀ z, z ∈ remaining.erase deficit →
            (afterOpening (remaining.erase deficit) z).value = .loss → z = y := by
  let position : Position := ⟨remaining, deficit⟩
  have hremaining : position.remaining ≠ ∅ := by
    exact Finset.nonempty_iff_ne_empty.mp ⟨deficit, hdeficit⟩
  have hsum : deficit ≤ position.remaining.sum (fun x ↦ x) := by
    exact Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hdeficit
  have hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit := by
    simpa [position] using (not_lt_of_ge hsum)
  have hmoveDeficit : position.moveOutcome deficit = .loss := by
    exact move_outcome_eq_loss_of_value_eq_loss position hremaining hcatch deficit
      hdeficit hloss
  have htiedPositionWin : Position.value ⟨remaining.erase deficit, 0⟩ = .win := by
    have hafter : position.afterPick deficit = ⟨remaining.erase deficit, 0⟩ := by
      simp [position, Position.afterPick]
    rw [Position.moveOutcome, hafter] at hmoveDeficit
    simp only [position, lt_self_iff_false, ite_false] at hmoveDeficit
    cases hvalue : Position.value ⟨remaining.erase deficit, 0⟩ <;>
      simp [hvalue, Outcome.neg] at hmoveDeficit ⊢
  have htiedWin : value (remaining.erase deficit) = .win := by
    rw [← position_value_tied_eq_value]
    exact htiedPositionWin
  have htiedNonempty : (remaining.erase deficit).Nonempty := by
    by_contra hempty
    have herase : remaining.erase deficit = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [herase, Position.value.eq_def] at htiedPositionWin
    simp at htiedPositionWin
  refine ⟨htiedWin, ?_⟩
  obtain ⟨y, hyWin, hyUnique⟩ :=
    (value_eq_win_iff_exists_unique_winning_opening
      (remaining.erase deficit) htiedNonempty).mp htiedWin
  refine ⟨y, hyWin.1, hyWin.2, ?_, ?_⟩
  · have hyNe : y ≠ deficit := Finset.ne_of_mem_erase hyWin.1
    rcases lt_or_gt_of_ne hyNe with hyLt | hyGt
    · exfalso
      let intermediate : Position := position.afterPick y
      have hyRemaining : y ∈ position.remaining := Finset.mem_of_mem_erase hyWin.1
      have hintermediateLoss : intermediate.value = .loss := by
        have hmoveY : position.moveOutcome y = .loss := by
          exact move_outcome_eq_loss_of_value_eq_loss position hremaining hcatch y
            hyRemaining hloss
        simpa [intermediate, Position.moveOutcome, position, hyLt] using hmoveY
      have hdIntermediate : deficit ∈ intermediate.remaining := by
        simp [intermediate, position, Position.afterPick, hdeficit, Ne.symm hyNe]
      have hintermediateRemaining : intermediate.remaining ≠ ∅ := by
        exact Finset.nonempty_iff_ne_empty.mp ⟨deficit, hdIntermediate⟩
      have hintermediateSum : deficit ≤ intermediate.remaining.sum (fun x ↦ x) := by
        exact Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hdIntermediate
      have hintermediateCatch :
          ¬ intermediate.remaining.sum (fun x ↦ x) < intermediate.deficit := by
        have hdeficitEq : intermediate.deficit = deficit - y := by
          simp [intermediate, position, Position.afterPick, hyLt]
        rw [hdeficitEq]
        omega
      have hmoveD : intermediate.moveOutcome deficit = .loss := by
        exact move_outcome_eq_loss_of_value_eq_loss intermediate hintermediateRemaining
          hintermediateCatch deficit hdIntermediate hintermediateLoss
      have hafter : intermediate.afterPick deficit =
          afterOpening (remaining.erase deficit) y := by
        have hdNotLt : ¬ deficit < deficit - y := by omega
        simp [intermediate, position, Position.afterPick, afterOpening, hyLt,
          hdNotLt, Finset.erase_right_comm]
        omega
      have hdcatch : ¬ deficit < intermediate.deficit := by
        simp [intermediate, position, Position.afterPick, hyLt]
      simp only [Position.moveOutcome, hdcatch, ite_false, hafter, hyWin.2,
        Outcome.neg] at hmoveD
      cases hmoveD
    · exact hyGt
  · intro z hz hzwins
    exact hyUnique z ⟨hz, hzwins⟩

/-- A player cannot lose when their deficit is an available maximum counter. -/
theorem Position.value_ne_loss_of_deficit_is_max
    (remaining : Finset ℕ) (deficit : ℕ)
    (hdeficit : deficit ∈ remaining)
    (hmax : ∀ x ∈ remaining, x ≤ deficit) :
    Position.value ⟨remaining, deficit⟩ ≠ .loss := by
  intro hloss
  obtain ⟨_, y, hy, _, hlarge, _⟩ :=
    loss_with_available_deficit_forces_large_unique_winning_opening
      remaining deficit hdeficit hloss
  exact (not_lt_of_ge (hmax y (Finset.mem_of_mem_erase hy))) hlarge

/-- The top member of the lower pair-deletion ray is always nonlosing. -/
theorem pair_deletion_position_top_value_ne_loss
    (N : ℕ) (hN : 3 ≤ N) :
    (pairDeletionPosition N 1 N).value ≠ .loss := by
  apply Position.value_ne_loss_of_deficit_is_max
  · simp
    omega
  · intro x hx
    simp only [Finset.mem_erase, Finset.mem_Icc] at hx
    omega

/-- To rule out a lower-ray loss, it suffices to rule out every winning opening strictly above
the available exact deficit. -/
theorem pair_deletion_position_value_ne_loss_of_upper_residuals
    (N b : ℕ) (hb : 3 ≤ b) (hbN : b ≤ N)
    (hupper : ∀ y ∈ Finset.Icc (b + 1) N,
      (afterOpening
        ((((Finset.Icc 1 N).erase 1).erase b).erase (b - 1)) y).value ≠ .loss) :
    (pairDeletionPosition N 1 b).value ≠ .loss := by
  intro hloss
  let remaining := ((Finset.Icc 1 N).erase 1).erase b
  have hdeficit : b - 1 ∈ remaining := by
    simp [remaining]
    omega
  obtain ⟨_, y, hyResidual, hyLoss, hyLarger, _⟩ :=
    loss_with_available_deficit_forces_large_unique_winning_opening
      remaining (b - 1) hdeficit (by simpa [remaining, pairDeletionPosition] using hloss)
  have hyUpper : y ∈ Finset.Icc (b + 1) N := by
    simp only [remaining, Finset.mem_erase, Finset.mem_Icc] at hyResidual
    simp only [Finset.mem_Icc]
    omega
  exact (hupper y hyUpper) (by simpa [remaining] using hyLoss)

/-- A losing post-opening position with both adjacent counters available forces an extreme
loss-to-win jump between the two resulting deficit-one states. -/
theorem after_opening_loss_forces_neighbor_value_jump
    (S : Finset ℕ) (y : ℕ) (hy : 0 < y)
    (hprev : y - 1 ∈ S) (hnext : y + 1 ∈ S)
    (hloss : (afterOpening S y).value = .loss) :
    Position.value ⟨(S.erase (y - 1)).erase y, 1⟩ = .loss ∧
      Position.value ⟨(S.erase y).erase (y + 1), 1⟩ = .win := by
  let position := afterOpening S y
  have hprevNe : y - 1 ≠ y := by omega
  have hnextNe : y + 1 ≠ y := by omega
  have hprevRemaining : y - 1 ∈ position.remaining := by
    exact Finset.mem_erase.mpr ⟨hprevNe, hprev⟩
  have hnextRemaining : y + 1 ∈ position.remaining := by
    exact Finset.mem_erase.mpr ⟨hnextNe, hnext⟩
  have hremaining : position.remaining ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨y - 1, hprevRemaining⟩
  have hsum : y + 1 ≤ position.remaining.sum (fun x ↦ x) :=
    Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hnextRemaining
  have hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit := by
    change ¬ position.remaining.sum (fun x ↦ x) < y
    omega
  have hmovePrev : position.moveOutcome (y - 1) = .loss :=
    move_outcome_eq_loss_of_value_eq_loss position hremaining hcatch (y - 1)
      hprevRemaining hloss
  have hmoveNext : position.moveOutcome (y + 1) = .loss :=
    move_outcome_eq_loss_of_value_eq_loss position hremaining hcatch (y + 1)
      hnextRemaining hloss
  have hsubPrev : y - (y - 1) = 1 := by omega
  constructor
  · simpa [position, Position.moveOutcome, Position.afterPick, afterOpening,
      show y - 1 < y by omega, hsubPrev, Finset.erase_right_comm] using hmovePrev
  · have hneg : (Position.value ⟨(S.erase y).erase (y + 1), 1⟩).neg = .loss := by
      simpa [position, Position.moveOutcome, Position.afterPick, afterOpening,
        show ¬ y + 1 < y by omega] using hmoveNext
    cases hvalue : Position.value ⟨(S.erase y).erase (y + 1), 1⟩ <;>
      simp [hvalue, Outcome.neg] at hneg ⊢

/-- The tied residual obtained by removing a successor child's exact deficit. -/
def lowerRaySuccessorChildTiedResidual (N b x : ℕ) : Finset ℕ :=
  ((((Finset.Icc 2 N).erase b).erase (b + 1)).erase x).erase (x - 2)

/-- If a successor child is losing while its exact deficit remains available, its tied residual is
winning and its globally unique winning opening lies above that deficit. -/
theorem lower_ray_successor_child_loss_forces_large_unique_winning_opening
    (N b x : ℕ)
    (hdeficit : x - 2 ∈ (lowerRaySuccessorChild N b x).remaining)
    (hloss : (lowerRaySuccessorChild N b x).value = .loss) :
    value (lowerRaySuccessorChildTiedResidual N b x) = .win ∧
      ∃ y, y ∈ lowerRaySuccessorChildTiedResidual N b x ∧
        (afterOpening (lowerRaySuccessorChildTiedResidual N b x) y).value = .loss ∧
          x - 2 < y ∧
            ∀ z, z ∈ lowerRaySuccessorChildTiedResidual N b x →
              (afterOpening (lowerRaySuccessorChildTiedResidual N b x) z).value = .loss →
                z = y := by
  simpa [lowerRaySuccessorChild, lowerRaySuccessorChildTiedResidual] using
    loss_with_available_deficit_forces_large_unique_winning_opening
      (lowerRaySuccessorChild N b x).remaining (x - 2) hdeficit hloss

end CatchUp
