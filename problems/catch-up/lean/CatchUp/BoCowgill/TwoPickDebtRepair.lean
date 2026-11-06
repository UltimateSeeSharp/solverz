/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/TwoPickDebtRepair.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.TwoBufferProtocol

/-!
# Two-pick preparation and copied-pair debt repair

The mandatory actual prefix [2, 11] requires a new repair: take 5 then 9 in
the same protected turn. This is the k = 2 instance of the preparation below.
Every strictly winning shadow bridge reply is forced. Both games then share
two counters, with deficits differing by two. Copying the opponent's revealed
pick gives legal terminal traces with an exact completed-margin difference.

These arithmetic transition lemmas do not assume the Catch-Up conjecture or
assert that arbitrary adjacent-hole roots can reach this family.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.TwoBuffer
/-- The sole legal pick ties the scores, so player two cannot lose. -/
theorem singleton_tie_safe (a : ℕ) :
    CanAvoidLoss .p2 ⟨⟨{a}, a⟩, .p1⟩ := by
  rw [can_avoid_loss_iff_forall_safe_moves _ _
    (by simp [GamePosition.IsTerminal]) (by simp)]
  intro x hx
  have he : x = a := by simpa [GamePosition.LegalMove] using hx
  subst x
  simp [GamePosition.afterPick, Position.afterPick, Player.other, CanAvoidLoss.eq_def,
    GamePosition.IsTerminal, GamePosition.terminalOutcomeFor]

/-- Taking the larger of two counters whose difference is the deficit forces a draw. -/
theorem pair_draw_reply (a d : ℕ) (hd : 0 < d) :
    CanAvoidLoss .p2 ⟨⟨{a, a + d}, d⟩, .p2⟩ := by
  apply (can_avoid_loss_iff_exists_safe_move .p2 ⟨⟨{a, a + d}, d⟩, .p2⟩ ?_ rfl).mpr
  · refine ⟨a + d, by simp [GamePosition.LegalMove], ?_⟩
    convert singleton_tie_safe a using 1
    · simp (disch := omega) [GamePosition.afterPick, Position.afterPick, Player.other,
        Finset.erase_insert_of_ne]
  · simp (disch := (simp only [Finset.mem_singleton]; omega))
      [GamePosition.IsTerminal, Finset.sum_insert]
    omega

/-- Every strictly winning protected bridge reply must take the largest counter. -/
theorem bridge_forced_parametric (k x : ℕ)
    (hx : (⟨⟨{k + 4, 2 * k + 6, 2 * k + 7}, k + 3⟩, .p1⟩ : GamePosition).LegalMove x)
    (hw : ¬CanAvoidLoss .p2
      ((⟨⟨{k + 4, 2 * k + 6, 2 * k + 7}, k + 3⟩, .p1⟩ : GamePosition).afterPick x)) :
    x = 2 * k + 7 := by
  simp only [GamePosition.LegalMove, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | h
  · exfalso
    apply hw
    convert pair_draw_reply (2 * k + 6) 1 (by omega) using 1
    · simp (disch := omega) [GamePosition.afterPick, Position.afterPick, Player.other]
      omega
  · exfalso
    apply hw
    have hadd : k + 4+(k + 3) = 2 * k + 7 := by omega
    convert pair_draw_reply (k + 4) (k + 3) (by omega) using 1
    · simp (disch := first | omega |
        (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
        [hadd, GamePosition.afterPick, Position.afterPick, Player.other, Finset.erase_insert_of_ne,
          Finset.erase_eq_of_notMem]
      split_ifs <;> omega
  · exact h

/-- Two picks consume the pair when both picks reach the opposing score. -/
theorem two_pick_trace (x z d : ℕ) (hne : x ≠ z) (hd : d ≤ x) (hc : x ≤ d + z) :
    GamePosition.PickTrace ⟨⟨{x, z}, d⟩, .p2⟩ [x, z]
      ⟨⟨∅, d + z - x⟩, .p2⟩ := by
  apply GamePosition.PickTrace.cons
  · apply GamePosition.step_after_pick
    · simp (disch := (simp only [Finset.mem_singleton]; omega))
        [GamePosition.IsTerminal, Finset.sum_insert]
      omega
    · simp [GamePosition.LegalMove]
  · have he : (⟨⟨{x, z}, d⟩, .p2⟩ : GamePosition).afterPick x =
        ⟨⟨{z}, x - d⟩, .p1⟩ := by
      simp [GamePosition.afterPick, Position.afterPick, Player.other, not_lt_of_ge hd, hne]
    rw [he]
    apply GamePosition.PickTrace.cons
    · apply GamePosition.step_after_pick
      · simp [GamePosition.IsTerminal]
        omega
      · simp [GamePosition.LegalMove]
    · have he2 : (⟨⟨{z}, x - d⟩, .p1⟩ : GamePosition).afterPick z =
          ⟨⟨∅, d + z - x⟩, .p2⟩ := by
        simp [GamePosition.afterPick, Position.afterPick, Player.other]
        split_ifs <;> omega
      rw [he2]
      exact GamePosition.PickTrace.nil _

/-- Copying the pair preserves an exact margin debt of two and gives actual nonloss. -/
theorem copied_pair_repair (x z d : ℕ) (hne : x ≠ z)
    (hd : d + 2 ≤ x) (hc : x ≤ d + z) :
    GamePosition.PickTrace ⟨⟨{x, z}, d⟩, .p2⟩ [x, z] ⟨⟨∅, d + z - x⟩, .p2⟩ ∧
    GamePosition.PickTrace ⟨⟨{x, z}, d + 2⟩, .p2⟩ [x, z] ⟨⟨∅, d + 2 + z - x⟩, .p2⟩ ∧
    (⟨⟨∅, d + z - x⟩, .p2⟩ : GamePosition).completedMargin .p1 + 2 =
      (⟨⟨∅, d + 2 + z - x⟩, .p2⟩ : GamePosition).completedMargin .p1 ∧
    0 ≤ (⟨⟨∅, d + z - x⟩, .p2⟩ : GamePosition).completedMargin .p1 := by
  refine ⟨two_pick_trace x z d hne (by omega) hc,
    two_pick_trace x z (d + 2) hne hd (by omega), ?_⟩
  simp only [GamePosition.completedMargin, GamePosition.p1ScoreBalance,
    Player.scoreCoefficient, Finset.sum_empty]
  norm_num
  omega

/-- After one counter of a distinct pair is removed, the remaining reply is forced. -/
theorem pair_reply_forced (x z d r : ℕ) (hne : x ≠ z)
    (hr : ((⟨⟨{x, z}, d⟩, .p2⟩ : GamePosition).afterPick x).LegalMove r) : r = z := by
  simpa [GamePosition.LegalMove, GamePosition.afterPick, Position.afterPick, hne] using hr

/-- Actual state before the two protected preparation picks. -/
def preparationRoot (k : ℕ) : GamePosition :=
  ⟨⟨{k + 3, k + 4, 2 * k + 5, 2 * k + 6}, 2 * k + 6⟩, .p1⟩

/-- The first preparation pick remains within the protected player's turn. -/
theorem preparation_first (k : ℕ) :
    (preparationRoot k).afterPick (k + 3) =
      ⟨⟨{k + 4, 2 * k + 5, 2 * k + 6}, k + 3⟩, .p1⟩ := by
  simp (disch := first | omega |
      (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
    [preparationRoot, GamePosition.afterPick, Position.afterPick]
  split_ifs <;> omega

/-- The second preparation pick switches to the opponent on the common pair. -/
theorem preparation_second (k : ℕ) :
    (⟨⟨{k + 4, 2 * k + 5, 2 * k + 6}, k + 3⟩, .p1⟩ : GamePosition).afterPick (2 * k + 5) =
      ⟨⟨{k + 4, 2 * k + 6}, k + 2⟩, .p2⟩ := by
  simp (disch := first | omega |
      (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
    [GamePosition.afterPick, Position.afterPick, Player.other,
      Finset.erase_insert_of_ne, Finset.erase_eq_of_notMem]
  split_ifs <;> omega

/-- Two protected picks legally prepare the common two-counter support. -/
theorem preparation_turn (k : ℕ) :
    CompletedTurn (preparationRoot k) [k + 3, 2 * k + 5]
      ⟨⟨{k + 4, 2 * k + 6}, k + 2⟩, .p2⟩ := by
  apply CompletedTurn.more
  · simp [preparationRoot, GamePosition.LegalMove]
  · simp [preparationRoot]
    omega
  · rw [preparation_first]
    convert CompletedTurn.finish (⟨⟨{k + 4, 2 * k + 5, 2 * k + 6}, k + 3⟩, .p1⟩ : GamePosition)
      (2 * k + 5) (by simp [GamePosition.LegalMove]) (by simp; omega) using 1
    exact (preparation_second k).symm

/-- Both opponent picks satisfy the copied-pair repair inequalities. -/
theorem repaired_pair_all_choices (k x : ℕ) (hx : x ∈ ({k + 4, 2 * k + 6} : Finset ℕ)) :
    ∃ z, ({x, z} : Finset ℕ) = {k + 4, 2 * k + 6} ∧ x ≠ z ∧ k + 2+2 ≤ x ∧
      x ≤ k + 2+z := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨2 * k + 6, rfl, by omega, by omega, by omega⟩
  · exact ⟨k + 4, Finset.pair_comm _ _, by omega, by omega, by omega⟩

/-- Actual prefix [2, 11] reaches the parametric preparation at k = 2. -/
theorem mandatory_eleven_preparation :
    (⟨AdjacentHoleExchange.exchangeLeft, .p1⟩ : GamePosition).afterPicks [2, 11] =
      preparationRoot 2 := by
  decide +kernel

/-- The shadow setup immediately before the opponent's bridge pick. -/
def shadowPreparationRoot (k : ℕ) : GamePosition :=
  ⟨⟨{k + 4, k + 5, 2 * k + 6, 2 * k + 7}, 2⟩, .p2⟩

/-- The shadow opponent bridge pick reaches the forced-reply triple. -/
theorem shadow_preparation_first (k : ℕ) :
    (shadowPreparationRoot k).afterPick (k + 5) =
      ⟨⟨{k + 4, 2 * k + 6, 2 * k + 7}, k + 3⟩, .p1⟩ := by
  simp (disch := first | omega |
      (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
    [shadowPreparationRoot, GamePosition.afterPick, Position.afterPick, Player.other,
      Finset.erase_insert_of_ne, Finset.erase_eq_of_notMem]

/-- The forced protected bridge reply reaches the common pair with debt two. -/
theorem shadow_preparation_second (k : ℕ) :
    (⟨⟨{k + 4, 2 * k + 6, 2 * k + 7}, k + 3⟩, .p1⟩ : GamePosition).afterPick (2 * k + 7) =
      ⟨⟨{k + 4, 2 * k + 6}, k + 4⟩, .p2⟩ := by
  simp (disch := first | omega |
      (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
    [GamePosition.afterPick, Position.afterPick, Player.other,
      Finset.erase_insert_of_ne]
  split_ifs <;> omega

/-- Shadow prefix [5, 2] reaches the parametric shadow preparation at k = 2. -/
theorem mandatory_shadow_preparation :
    (⟨AdjacentHoleExchange.exchangeRight, .p1⟩ : GamePosition).afterPicks [5, 2] =
      shadowPreparationRoot 2 := by
  decide +kernel

/-- The shadow bridge consists of two legal completed turns, including at k = 0. -/
theorem shadow_preparation_trace (k : ℕ) :
    GamePosition.PickTrace (shadowPreparationRoot k) [k + 5, 2 * k + 7]
      ⟨⟨{k + 4, 2 * k + 6}, k + 4⟩, .p2⟩ := by
  have firstTurn := CompletedTurn.finish (shadowPreparationRoot k) (k + 5)
    (by simp [shadowPreparationRoot, GamePosition.LegalMove]) (by simp [shadowPreparationRoot])
  have secondTurn := CompletedTurn.finish
    (⟨⟨{k + 4, 2 * k + 6, 2 * k + 7}, k + 3⟩, .p1⟩ : GamePosition) (2 * k + 7)
    (by simp [GamePosition.LegalMove]) (by simp; omega)
  apply GamePosition.PickTrace.cons
  · exact GamePosition.step_after_pick _ _ firstTurn.before_not_terminal
      (by simp [shadowPreparationRoot, GamePosition.LegalMove])
  · rw [shadow_preparation_first]
    simpa only [shadow_preparation_second] using secondTurn.pick_trace

end CatchUp.TwoBuffer
