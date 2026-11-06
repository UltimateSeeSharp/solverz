/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/FirstPairDescentObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.CompletedTurn
public import CatchUp.BoCowgill.Earlier.CompletedMargin
public import CatchUp.BoCowgill.PairDeletion
public import CatchUp.BoCowgill.Classifier

/-!
# First-pair strategy-stealing identities and obstructions

This module verifies the endpoint definition, first-pick polarity, and two small bases.
It refutes a geometry-free three-reserve transfer and certifies a common-pick copying
failure along legal size-eight prefixes. It does not prove the uniform interval endpoint.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.FirstPairDescent
/-- The first pair-deletion endpoint, viewed from the current mover. -/
def root (N : ℕ) : Position := ⟨Finset.Icc 3 N, 1⟩
/-- Deleting one and two from the interval is exactly the requested tail at deficit one. -/
theorem root_eq_pair (N : ℕ) : root N = pairDeletionPosition N 1 2 := by
  change (⟨Finset.Icc 3 N, 1⟩ : Position) = _
  rw [pairDeletionPosition, Position.mk.injEq]
  constructor
  · ext x
    simp
    omega
  · rfl

/-- Every available first pick catches and transfers the move to player two. -/
theorem first_pick (N x : ℕ) (hx : x ∈ Finset.Icc 3 N) :
    (⟨root N, .p1⟩ : GamePosition).afterPick x =
      ⟨⟨(Finset.Icc 3 N).erase x, x - 1⟩, .p2⟩ := by
  have h : ¬ x < 1 := by have := (Finset.mem_Icc.mp hx).1; omega
  simp [GamePosition.afterPick, Position.afterPick, root, h, Player.other]

/-- A positive first pick from a losing deficit-one position leaves a winning child. -/
theorem deficit_one_loss_child_win (S : Finset ℕ) (x : ℕ)
    (hx : x ∈ S) (hpos : 1 ≤ x)
    (hloss : (⟨S, 1⟩ : Position).value = .loss) :
    (⟨S.erase x, x - 1⟩ : Position).value = .win := by
  let p : Position := ⟨S, 1⟩
  have hn : p.remaining ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩
  have hsum : x ≤ S.sum (fun y ↦ y) :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  have hc : ¬ p.remaining.sum (fun y ↦ y) < p.deficit := by dsimp [p]; omega
  have hm : p.moveOutcome x = .loss := by
    by_contra hmove
    have hb : Outcome.best (p.remaining.attach.toList.map
        fun move ↦ p.moveOutcome move.1) ≠ .loss := by
      rw [Outcome.best_ne_loss_iff]
      refine ⟨p.moveOutcome x, ?_, hmove⟩
      exact List.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
    exact hb ((Position.value_eq_best_move_outcome p hn hc).symm.trans hloss)
  have hlt : ¬ x < 1 := by omega
  simp only [Position.moveOutcome, p, hlt, ite_false, Position.afterPick] at hm
  cases hv : (⟨S.erase x, x - 1⟩ : Position).value <;>
    simp_all [Outcome.neg]

/-- A hypothetical endpoint loss forces all its first-pick children to win. -/
theorem loss_forces_all_first_children_win (N : ℕ)
    (hloss : (root N).value = .loss) :
    ∀ x ∈ Finset.Icc 3 N,
      (⟨(Finset.Icc 3 N).erase x, x - 1⟩ : Position).value = .win := by
  intro x hx
  exact deficit_one_loss_child_win _ _ hx (by
    have := (Finset.mem_Icc.mp hx).1
    omega) hloss

private def checkedValue (p : Position) : Outcome :=
  if CatchUpSearch.CanAvoidLossClassifier.check .p1 ⟨p, .p1⟩ then
    if CatchUpSearch.CanAvoidLossClassifier.check .p2 ⟨p, .p1⟩ then .draw else .win
  else .loss
private theorem checked_value_eq (p : Position) : checkedValue p = p.value := by
  have h₁ := (CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff .p1 ⟨p, .p1⟩).trans
    (can_avoid_loss_iff_value .p1 ⟨p, .p1⟩)
  have h₂ := (CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff .p2 ⟨p, .p1⟩).trans
    (can_avoid_loss_iff_value .p2 ⟨p, .p1⟩)
  cases h : p.value <;> simp_all [checkedValue]

/-- Direct kernel evaluation of the endpoint at seven, not an interval-root certificate. -/
theorem base_seven : (root 7).value = .draw := by
  rw [← checked_value_eq]
  decide +kernel
/-- Direct kernel evaluation of the endpoint at eight. -/
theorem base_eight : (root 8).value = .draw := by
  rw [← checked_value_eq]
  decide +kernel

/-- A sparse support with minimum three and even effective total. It is not an interval. -/
def sparse : Finset ℕ := {3, 7, 9, 14, 17, 20, 29, 34}
/-- The sparse deficit-one position loses; interval geometry cannot be discarded. -/
theorem sparse_loss : (⟨sparse, 1⟩ : Position).value = .loss := by
  rw [← checked_value_eq]
  decide +kernel
/-- Deleting three produces a strictly winning deficit-two shadow. -/
theorem sparse_shadow_win : (⟨sparse.erase 3, 2⟩ : Position).value = .win := by
  simpa using deficit_one_loss_child_win sparse 3 (by decide +kernel)
    (by omega) sparse_loss

/-- The sparse example meets the minimum-counter and effective-parity conditions. -/
theorem sparse_structure :
    3 ∈ sparse ∧ (∀ x ∈ sparse, 3 ≤ x) ∧
      Even (1 + sparse.sum id) := by
  decide +kernel

/-- No transfer based only on minimum three and parity can handle all such supports. -/
theorem no_geometry_free_three_reserve_transfer :
    ¬ (∀ S : Finset ℕ, 3 ∈ S → (∀ x ∈ S, 3 ≤ x) →
      Even (1 + S.sum id) →
      (⟨S.erase 3, 2⟩ : Position).value = .win →
      (⟨S, 1⟩ : Position).value ≠ .loss) := by
  intro h
  exact h sparse sparse_structure.1 sparse_structure.2.1 sparse_structure.2.2
    sparse_shadow_win sparse_loss

/-- Raw reversal identities: deficits differ by two and the movers differ.
This statement concerns raw updates; it does not assert legality or nonterminality. -/
theorem raw_two_pick_exchange (S : Finset ℕ) (x y : ℕ)
    (hx : 1 ≤ x) (hxy : x + 1 < y) :
    (⟨⟨S, 1⟩, .p1⟩ : GamePosition).afterPicks [x,y] =
      ⟨⟨(S.erase x).erase y, y - x + 1⟩, .p1⟩ ∧
    (⟨⟨S, 1⟩, .p1⟩ : GamePosition).afterPicks [y,x] =
      ⟨⟨(S.erase x).erase y, y - x - 1⟩, .p2⟩ := by
  have hx1 : ¬ x < 1 := by omega
  have hy1 : ¬ y < 1 := by omega
  have hyx : ¬ y < x - 1 := by omega
  have hxy' : x < y - 1 := by omega
  have he1 : y - (x - 1) = y - x + 1 := by omega
  have he2 : y - 1 - x = y - x - 1 := by omega
  simp [GamePosition.afterPicks, GamePosition.afterPick, Position.afterPick,
    Player.other, hx1, hy1, hyx, hxy', he1, he2, Finset.erase_right_comm]

/-- The actual position after the common prefix five, seven at the size-eight root. -/
def actualBridge : Position := ⟨{3,4,6,8}, 3⟩
/-- The corresponding shadow, with counter three absent and deficit one larger. -/
def shadowBridge : Position := ⟨{4,6,8}, 4⟩

/-- Both bridge positions win before the attempted common-counter copy. -/
theorem bridge_values : actualBridge.value = .win ∧ shadowBridge.value = .win := by
  rw [← checked_value_eq actualBridge, ← checked_value_eq shadowBridge]
  decide +kernel

private theorem checked_bridge_moves :
    (∀ x : {x // x ∈ actualBridge.remaining},
      checkedValue (actualBridge.afterPick x) =
        if x.val = 4 then .draw else if x.val = 6 then .loss else .win) ∧
    (∀ x : {x // x ∈ shadowBridge.remaining},
      checkedValue (shadowBridge.afterPick x) =
        if x.val = 8 then .loss else .win) := by
  decide +kernel

/-- The only winning shadow bridge move is eight. -/
theorem bridge_shadow_win_forces_eight (x : ℕ) (hx : x ∈ shadowBridge.remaining)
    (hw : shadowBridge.moveOutcome x = .win) : x = 8 := by
  have hc : ¬ x < shadowBridge.deficit := by
    simp only [shadowBridge, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    omega
  rw [Position.moveOutcome, ite_eq_right hc, ← checked_value_eq,
    checked_bridge_moves.2 ⟨x,hx⟩] at hw
  split_ifs at hw <;> simp_all [Outcome.neg]

/-- Copying that winning shadow pick loses in the actual bridge. -/
theorem bridge_copy_eight_loses : actualBridge.moveOutcome 8 = .loss := by
  rw [Position.moveOutcome, ite_eq_right (by decide +kernel), ← checked_value_eq,
    checked_bridge_moves.1 ⟨8, by decide +kernel⟩]
  rfl

/-- A different actual pick wins, so the bridge itself is not a losing-state witness. -/
theorem bridge_actual_six_wins : actualBridge.moveOutcome 6 = .win := by
  rw [Position.moveOutcome, ite_eq_right (by decide +kernel), ← checked_value_eq,
    checked_bridge_moves.1 ⟨6, by decide +kernel⟩]
  rfl

private def legalPicks : GamePosition → List ℕ → Bool
  | _, [] => true
  | p, x :: xs => decide (¬p.IsTerminal) && decide (x ∈ p.remaining) &&
      legalPicks (p.afterPick x) xs
private theorem legal_picks_sound (p : GamePosition) (xs : List ℕ)
    (h : legalPicks p xs = true) : GamePosition.PickTrace p xs (p.afterPicks xs) := by
  induction xs generalizing p with
  | nil => exact GamePosition.PickTrace.nil p
  | cons x xs ih =>
    simp only [legalPicks, Bool.and_eq_true, decide_eq_true_eq] at h
    exact GamePosition.PickTrace.cons _ _ _ _
      (p.step_after_pick x h.1.1 h.1.2) (ih _ h.2)

/-- Both bridge positions follow legal common prefixes from the respective size-eight roots. -/
theorem bridge_legal_prefixes :
    GamePosition.PickTrace ⟨root 8, .p1⟩ [5,7] ⟨actualBridge,.p1⟩ ∧
    GamePosition.PickTrace ⟨⟨Finset.Icc 4 8, 2⟩,.p1⟩ [5,7] ⟨shadowBridge,.p1⟩ := by
  constructor
  · have h := legal_picks_sound ⟨root 8,.p1⟩ [5,7] (by decide +kernel)
    have he : (⟨root 8,.p1⟩ : GamePosition).afterPicks [5,7] =
        ⟨actualBridge,.p1⟩ := by decide +kernel
    exact he ▸ h
  · have h := legal_picks_sound ⟨⟨Finset.Icc 4 8,2⟩,.p1⟩ [5,7] (by decide +kernel)
    have he : (⟨⟨Finset.Icc 4 8,2⟩,.p1⟩ : GamePosition).afterPicks [5,7] =
        ⟨shadowBridge,.p1⟩ := by decide +kernel
    exact he ▸ h

/-- The copied eight switches to player two in both games, with deficits five and four. -/
theorem bridge_copied_endpoints :
    (⟨actualBridge,.p1⟩ : GamePosition).afterPick 8 =
      ⟨⟨{3,4,6},5⟩,.p2⟩ ∧
    (⟨shadowBridge,.p1⟩ : GamePosition).afterPick 8 =
      ⟨⟨{4,6},4⟩,.p2⟩ := by
  decide +kernel

/-- The sparse obstruction rules out every actual nonloss strategy, not only copying. -/
theorem sparse_has_no_nonloss_strategy :
    ¬ CanAvoidLoss .p1 ⟨⟨sparse,1⟩,.p1⟩ := by
  rw [can_avoid_loss_iff_value]
  simp [sparse_loss]

/-- The sparse counterexample also satisfies all simultaneous winning-child obligations. -/
theorem sparse_all_first_children_win :
    ∀ x ∈ sparse, (⟨sparse.erase x,x-1⟩ : Position).value = .win := by
  intro x hx
  exact deficit_one_loss_child_win sparse x hx (by
    have := sparse_structure.2.1 x hx
    omega) sparse_loss


/-- The deficit-two shadow is exactly the normalized child after taking three. -/
theorem shadow_after_three (N : ℕ) :
    (root N).afterPick 3 = (⟨Finset.Icc 4 N, 2⟩ : Position) := by
  simp only [root, Position.afterPick, show ¬ (3 : ℕ) < 1 by omega, ite_false]
  rw [Position.mk.injEq]
  constructor
  · ext x
    simp
    omega
  · rfl

/-- The shadow interval root used for the legal-prefix witness draws, rather than wins. -/
theorem bridge_shadow_root_draw :
    (⟨Finset.Icc 4 8, 2⟩ : Position).value = .draw := by
  rw [← checked_value_eq]
  decide +kernel


/-- The copied four switches the shadow mover but leaves the actual opponent one behind. -/
theorem bridge_owner_conflict :
    (⟨actualBridge,.p1⟩ : GamePosition).afterPicks [8,4] =
      ⟨⟨{3,6},1⟩,.p2⟩ ∧
    (⟨shadowBridge,.p1⟩ : GamePosition).afterPicks [8,4] =
      ⟨⟨{6},0⟩,.p1⟩ := by
  decide +kernel

/-- The same legal picks allocate six to opposite players and violate the proposed margin bound.
The actual game terminates early with counter three still available. -/
theorem bridge_completed_copy_obstruction :
    let u : GamePosition := ⟨actualBridge,.p1⟩
    let v : GamePosition := ⟨shadowBridge,.p1⟩
    GamePosition.PickTrace u [8,4,6] (u.afterPicks [8,4,6]) ∧
    GamePosition.PickTrace v [8,4,6] (v.afterPicks [8,4,6]) ∧
    (u.afterPicks [8,4,6]).IsTerminal ∧
    (v.afterPicks [8,4,6]).IsTerminal ∧
    (u.afterPicks [8,4,6]).completedMargin .p1 = -2 ∧
    (v.afterPicks [8,4,6]).completedMargin .p1 = 6 := by
  refine ⟨legal_picks_sound _ _ (by decide +kernel),
    legal_picks_sound _ _ (by decide +kernel), ?_⟩
  decide +kernel

end CatchUp.FirstPairDescent
