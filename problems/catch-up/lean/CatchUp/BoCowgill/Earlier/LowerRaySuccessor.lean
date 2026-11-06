/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/LowerRaySuccessor.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.PairDeletion

/-!
# Successor-move reduction for the lower pair-deletion ray

The move `b + 1` from the lower-ray state has the universal
overshoot `2`.  This file packages that identity, the resulting conditional interval reduction,
and the exact minimax obligations at the constant-deficit successor state.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- After taking `b + 1` from the lower-ray state, the opponent faces two adjacent holes and
constant deficit `2`. -/
def lowerRaySuccessorPosition (N b : ℕ) : Position :=
  ⟨((Finset.Icc 2 N).erase b).erase (b + 1), 2⟩

/-- A child of the constant-deficit successor state. -/
def lowerRaySuccessorChild (N b x : ℕ) : Position :=
  ⟨(((Finset.Icc 2 N).erase b).erase (b + 1)).erase x, x - 2⟩

/-- The successor counter is available at every non-top member of the lower ray. -/
theorem succ_mem_pair_deletion_position (N b : ℕ) (hb : 2 ≤ b) (hbN : b < N) :
    b + 1 ∈ (pairDeletionPosition N 1 b).remaining := by
  simp [pairDeletionPosition]
  omega

/-- Taking the successor counter from a lower-ray state gives universal deficit `2`. -/
theorem pair_deletion_position_after_pick_succ
    (N b : ℕ) (hb : 2 ≤ b) :
    (pairDeletionPosition N 1 b).afterPick (b + 1) = lowerRaySuccessorPosition N b := by
  simp only [pairDeletionPosition, lowerRaySuccessorPosition, Position.afterPick]
  have hcatch : ¬ b + 1 < b - 1 := by omega
  simp only [hcatch, ite_false]
  congr 1
  · ext x
    simp
    omega
  · omega

/-- The lower-ray successor move is the negated value of the constant-deficit state. -/
theorem pair_deletion_position_move_outcome_succ
    (N b : ℕ) (hb : 2 ≤ b) :
    (pairDeletionPosition N 1 b).moveOutcome (b + 1) =
      (lowerRaySuccessorPosition N b).value.neg := by
  rw [Position.moveOutcome]
  have hcatch : ¬ b + 1 < (pairDeletionPosition N 1 b).deficit := by
    simp [pairDeletionPosition]
    omega
  simp only [hcatch, ite_false]
  rw [pair_deletion_position_after_pick_succ N b hb]

/-- A nonwinning constant-deficit successor state makes the corresponding lower-ray state
nonlosing. -/
theorem pair_deletion_position_value_ne_loss_of_successor_value_ne_win
    (N b : ℕ) (hb : 2 ≤ b) (hbN : b < N)
    (hsuccessor : (lowerRaySuccessorPosition N b).value ≠ .win) :
    (pairDeletionPosition N 1 b).value ≠ .loss := by
  let position := pairDeletionPosition N 1 b
  have hsucc : b + 1 ∈ position.remaining := by
    exact succ_mem_pair_deletion_position N b hb hbN
  have hremaining : position.remaining ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨b + 1, hsucc⟩
  have hsum : b + 1 ≤ position.remaining.sum (fun x ↦ x) :=
    Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hsucc
  have hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit := by
    change ¬ position.remaining.sum (fun x ↦ x) < b - 1
    omega
  rw [Position.value_eq_best_move_outcome position hremaining hcatch,
    Outcome.best_ne_loss_iff]
  refine ⟨position.moveOutcome (b + 1), ?_, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨⟨b + 1, hsucc⟩, by simp, rfl⟩
  · rw [show position.moveOutcome (b + 1) =
        (lowerRaySuccessorPosition N b).value.neg by
      simpa [position] using pair_deletion_position_move_outcome_succ N b hb]
    exact (Outcome.neg_ne_loss_iff _).mpr hsuccessor

/-- Constant-deficit successor draws for all non-top members, plus a nonlosing top member, imply
the whole lower pair-deletion ray. -/
theorem lower_pair_deletion_nonloss_of_successor_draws
    (N : ℕ)
    (hsuccessor : ∀ b, 2 ≤ b → b < N →
      (lowerRaySuccessorPosition N b).value = .draw)
    (htop : (pairDeletionPosition N 1 N).value ≠ .loss) :
    LowerPairDeletionNonloss N := by
  intro b hbIcc hb
  have hbN : b ≤ N := (Finset.mem_Icc.mp hbIcc).2
  have hbTwo : 2 ≤ b := by omega
  rcases hbN.eq_or_lt with rfl | hbLt
  · exact htop
  · apply pair_deletion_position_value_ne_loss_of_successor_value_ne_win N b hbTwo hbLt
    rw [hsuccessor b hbTwo hbLt]
    simp

/-- Lower-ray assembly from non-loss at `b = 2`, successor nonwinning only for
`3 ≤ b < N`, and a separate top endpoint. -/
theorem lower_pair_deletion_nonloss_of_interior_successor_nonwin
    (N : ℕ)
    (hpairNonloss : (pairDeletionPosition N 1 2).value ≠ .loss)
    (hinterior : ∀ b, 3 ≤ b → b < N →
      (lowerRaySuccessorPosition N b).value ≠ .win)
    (htop : (pairDeletionPosition N 1 N).value ≠ .loss) :
    LowerPairDeletionNonloss N := by
  intro b hbIcc hb
  have hbN : b ≤ N := (Finset.mem_Icc.mp hbIcc).2
  by_cases hbTwo : b = 2
  · subst b
    exact hpairNonloss
  by_cases hbTop : b = N
  · subst b
    exact htop
  have hbThree : 3 ≤ b := by omega
  have hbLt : b < N := by omega
  exact pair_deletion_position_value_ne_loss_of_successor_value_ne_win N b
    (by omega) hbLt (hinterior b hbThree hbLt)

/-- The successor family, the top endpoint, and the usual first draw pair imply the interval draw. -/
theorem value_Icc_eq_draw_of_successor_draws
    (N : ℕ) (hN : 2 ≤ N)
    (hsuccessor : ∀ b, 2 ≤ b → b < N →
      (lowerRaySuccessorPosition N b).value = .draw)
    (htop : (pairDeletionPosition N 1 N).value ≠ .loss)
    (hpairDraw : (pairDeletionPosition N 1 2).value = .draw) :
    value (Finset.Icc 1 N) = .draw := by
  apply value_Icc_eq_draw_of_lower_pair_deletion_nonloss N hN
  · exact lower_pair_deletion_nonloss_of_successor_draws N hsuccessor htop
  · exact hpairDraw

/-- Successor nonwinning, a nonlosing top endpoint, and the first draw pair imply the interval
draw. -/
theorem value_Icc_eq_draw_of_interior_successor_nonwin
    (N : ℕ) (hN : 2 ≤ N)
    (hpairDraw : (pairDeletionPosition N 1 2).value = .draw)
    (hinterior : ∀ b, 3 ≤ b → b < N →
      (lowerRaySuccessorPosition N b).value ≠ .win)
    (htop : (pairDeletionPosition N 1 N).value ≠ .loss) :
    value (Finset.Icc 1 N) = .draw := by
  exact value_Icc_eq_draw_of_lower_pair_deletion_nonloss N hN
    (lower_pair_deletion_nonloss_of_interior_successor_nonwin
      N (by rw [hpairDraw]; simp) hinterior htop) hpairDraw

/-- Every legal move at the successor state catches immediately and reaches its named child. -/
theorem lower_ray_successor_move_outcome
    (N b x : ℕ) (hx : x ∈ (lowerRaySuccessorPosition N b).remaining) :
    (lowerRaySuccessorPosition N b).moveOutcome x =
      (lowerRaySuccessorChild N b x).value.neg := by
  have hxTwo : 2 ≤ x := by
    simp only [lowerRaySuccessorPosition, Finset.mem_erase, Finset.mem_Icc] at hx
    omega
  simp [Position.moveOutcome, lowerRaySuccessorPosition, lowerRaySuccessorChild,
    Position.afterPick, not_lt_of_ge hxTwo]

/-- After the exact reply `2`, an interior successor state leaves a tied root on
`{3,…,N} \ {b,b+1}`. -/
def lowerRaySuccessorTiedResidual (N b : ℕ) : Finset ℕ :=
  ((Finset.Icc 3 N).erase b).erase (b + 1)

private theorem position_value_tied_eq_value (S : Finset ℕ) :
    Position.value ⟨S, 0⟩ = value S := by
  rw [Position.value_eq_value_aux S 0 0 (by omega)]
  rw [value]
  rw [valueAux.eq_def, valueAux.eq_def]
  by_cases hS : S = ∅
  · simp [hS]
  · simp only [hS, Nat.zero_add, Nat.not_lt_zero, ite_false]
    congr 1

/-- The exact move `2` from an interior successor state is the negated tied-residual root value. -/
theorem lower_ray_successor_move_two
    (N b : ℕ) (hb : 3 ≤ b) :
    (lowerRaySuccessorPosition N b).moveOutcome 2 =
      (value (lowerRaySuccessorTiedResidual N b)).neg := by
  have hafter : (lowerRaySuccessorPosition N b).afterPick 2 =
      ⟨lowerRaySuccessorTiedResidual N b, 0⟩ := by
    simp only [lowerRaySuccessorPosition, lowerRaySuccessorTiedResidual, Position.afterPick]
    congr 1
    ext x
    simp
    omega
  rw [Position.moveOutcome]
  have hcatch : ¬ 2 < (lowerRaySuccessorPosition N b).deficit := by
    simp [lowerRaySuccessorPosition]
  simp only [hcatch, ite_false]
  rw [hafter, position_value_tied_eq_value]

private theorem successor_nonterminal
    (N b : ℕ) (hN : 4 ≤ N) (hb : 2 ≤ b) (hbN : b < N) :
    (lowerRaySuccessorPosition N b).remaining ≠ ∅ ∧
      ¬ (lowerRaySuccessorPosition N b).remaining.sum (fun x ↦ x) <
        (lowerRaySuccessorPosition N b).deficit := by
  by_cases hbTwo : b = 2
  · subst b
    have hfour : 4 ∈ (lowerRaySuccessorPosition N 2).remaining := by
      simp [lowerRaySuccessorPosition]
      omega
    constructor
    · exact Finset.nonempty_iff_ne_empty.mp ⟨4, hfour⟩
    · have hsum : 4 ≤ (lowerRaySuccessorPosition N 2).remaining.sum (fun x ↦ x) :=
        Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hfour
      change ¬ (lowerRaySuccessorPosition N 2).remaining.sum (fun x ↦ x) < 2
      omega
  · have htwo : 2 ∈ (lowerRaySuccessorPosition N b).remaining := by
      simp [lowerRaySuccessorPosition]
      omega
    constructor
    · exact Finset.nonempty_iff_ne_empty.mp ⟨2, htwo⟩
    · have hsum : 2 ≤ (lowerRaySuccessorPosition N b).remaining.sum (fun x ↦ x) :=
        Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) htwo
      change ¬ (lowerRaySuccessorPosition N b).remaining.sum (fun x ↦ x) < 2
      omega

/-- The successor state is nonlosing exactly when one three-hole child is nonwinning. -/
theorem lower_ray_successor_value_ne_loss_iff
    (N b : ℕ) (hN : 4 ≤ N) (hb : 2 ≤ b) (hbN : b < N) :
    (lowerRaySuccessorPosition N b).value ≠ .loss ↔
      ∃ x ∈ (lowerRaySuccessorPosition N b).remaining,
        (lowerRaySuccessorChild N b x).value ≠ .win := by
  obtain ⟨hremaining, hcatch⟩ := successor_nonterminal N b hN hb hbN
  rw [Position.value_eq_best_move_outcome _ hremaining hcatch,
    Outcome.best_ne_loss_iff]
  constructor
  · rintro ⟨outcome, houtcome, hnotloss⟩
    rcases List.mem_map.mp houtcome with ⟨⟨x, hx⟩, _, rfl⟩
    change (lowerRaySuccessorPosition N b).moveOutcome x ≠ .loss at hnotloss
    refine ⟨x, hx, ?_⟩
    rw [lower_ray_successor_move_outcome N b x hx,
      Outcome.neg_ne_loss_iff] at hnotloss
    exact hnotloss
  · rintro ⟨x, hx, hnotwin⟩
    refine ⟨(lowerRaySuccessorPosition N b).moveOutcome x, ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
    · rw [lower_ray_successor_move_outcome N b x hx,
        Outcome.neg_ne_loss_iff]
      exact hnotwin

/-- A nonwinning tied residual supplies the existential half of successor safety. -/
theorem lower_ray_successor_value_ne_loss_of_tied_residual_ne_win
    (N b : ℕ) (hN : 4 ≤ N) (hb : 3 ≤ b) (hbN : b < N)
    (hresidual : value (lowerRaySuccessorTiedResidual N b) ≠ .win) :
    (lowerRaySuccessorPosition N b).value ≠ .loss := by
  rw [lower_ray_successor_value_ne_loss_iff N b hN (by omega) hbN]
  refine ⟨2, ?_, ?_⟩
  · simp [lowerRaySuccessorPosition]
    omega
  · have hchild : lowerRaySuccessorChild N b 2 =
        ⟨lowerRaySuccessorTiedResidual N b, 0⟩ := by
      simp only [lowerRaySuccessorChild, lowerRaySuccessorTiedResidual]
      congr 1
      ext x
      simp
      omega
    rw [hchild, position_value_tied_eq_value]
    exact hresidual

/-- The successor state is nonwinning exactly when every three-hole child is nonlosing. -/
theorem lower_ray_successor_value_ne_win_iff
    (N b : ℕ) (hN : 4 ≤ N) (hb : 2 ≤ b) (hbN : b < N) :
    (lowerRaySuccessorPosition N b).value ≠ .win ↔
      ∀ x ∈ (lowerRaySuccessorPosition N b).remaining,
        (lowerRaySuccessorChild N b x).value ≠ .loss := by
  obtain ⟨hremaining, hcatch⟩ := successor_nonterminal N b hN hb hbN
  rw [Position.value_eq_best_move_outcome _ hremaining hcatch,
    Outcome.best_ne_win_iff]
  constructor
  · intro h x hx
    have hmove : (lowerRaySuccessorPosition N b).moveOutcome x ≠ .win := by
      apply h
      apply List.mem_map.mpr
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
    rw [lower_ray_successor_move_outcome N b x hx,
      Outcome.neg_ne_win_iff] at hmove
    exact hmove
  · intro h outcome houtcome
    rcases List.mem_map.mp houtcome with ⟨⟨x, hx⟩, _, rfl⟩
    change (lowerRaySuccessorPosition N b).moveOutcome x ≠ .win
    rw [lower_ray_successor_move_outcome N b x hx,
      Outcome.neg_ne_win_iff]
    exact h x hx

/-- Exact minimax characterization of a drawn constant-deficit successor state. -/
theorem lower_ray_successor_value_eq_draw_iff
    (N b : ℕ) (hN : 4 ≤ N) (hb : 2 ≤ b) (hbN : b < N) :
    (lowerRaySuccessorPosition N b).value = .draw ↔
      (∃ x ∈ (lowerRaySuccessorPosition N b).remaining,
          (lowerRaySuccessorChild N b x).value ≠ .win) ∧
        (∀ x ∈ (lowerRaySuccessorPosition N b).remaining,
          (lowerRaySuccessorChild N b x).value ≠ .loss) := by
  rw [Outcome.eq_draw_iff,
    lower_ray_successor_value_ne_loss_iff N b hN hb hbN,
    lower_ray_successor_value_ne_win_iff N b hN hb hbN]


end CatchUp
