/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseLossInjection.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.ExactSumLossObstruction

/-!
# Dense-loss complement-pair obstruction

This module records bounded-hole consequences of the exact-sum obstruction for a hypothetical
losing Catch-Up position. It isolates the only non-increasing cases as explicit small-deficit,
prefix-blocked losses.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

private theorem Position.loss_after_continuing_pick_of_value_eq_loss
    (position : Position) {x : ℕ}
    (hx : x ∈ position.remaining)
    (hcatch : ¬ position.remaining.sum (fun y => y) < position.deficit)
    (hxd : x < position.deficit)
    (hloss : position.value = .loss) :
    (position.afterPick x).value = .loss := by
  have hremaining : position.remaining ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩
  have hmove : position.moveOutcome x = .loss := by
    by_contra hmove
    have hbestNe :
        Outcome.best
            (position.remaining.attach.toList.map fun move =>
              position.moveOutcome move.1) ≠ .loss := by
      rw [Outcome.best_ne_loss_iff]
      refine ⟨position.moveOutcome x, ?_, hmove⟩
      apply List.mem_map.mpr
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
    rw [Position.value_eq_best_move_outcome position hremaining hcatch] at hloss
    exact hbestNe hloss
  simpa [Position.moveOutcome, hxd] using hmove

private theorem four_holes_of_three_blocked_pairs
    (N d : ℕ) (remaining : Finset ℕ) (a b c : ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (haShape : a = 1 ∨ a = d - 1)
    (hbShape : b = 2 ∨ b = d - 2)
    (hcShape : c = 3 ∨ c = d - 3)
    (hdMissing : d ∉ remaining)
    (haMissing : a ∉ remaining)
    (hbMissing : b ∉ remaining)
    (hcMissing : c ∉ remaining) :
    4 ≤ ((Finset.Icc 1 N) \ remaining).card := by
  have hsubset : ({d, a, b, c} : Finset ℕ) ⊆ (Finset.Icc 1 N) \ remaining := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨by simp; omega, hdMissing⟩
    · apply Finset.mem_sdiff.mpr
      constructor
      · rcases haShape with rfl | rfl <;> simp <;> omega
      · exact haMissing
    · apply Finset.mem_sdiff.mpr
      constructor
      · rcases hbShape with rfl | rfl <;> simp <;> omega
      · exact hbMissing
    · apply Finset.mem_sdiff.mpr
      constructor
      · rcases hcShape with rfl | rfl <;> simp <;> omega
      · exact hcMissing
  have hcard : ({d, a, b, c} : Finset ℕ).card = 4 := by
    have hda : d ≠ a := by rcases haShape with rfl | rfl <;> omega
    have hdb : d ≠ b := by rcases hbShape with rfl | rfl <;> omega
    have hdc : d ≠ c := by rcases hcShape with rfl | rfl <;> omega
    have hab : a ≠ b := by
      rcases haShape with rfl | rfl <;> rcases hbShape with rfl | rfl <;> omega
    have hac : a ≠ c := by
      rcases haShape with rfl | rfl <;> rcases hcShape with rfl | rfl <;> omega
    have hbc : b ≠ c := by
      rcases hbShape with rfl | rfl <;> rcases hcShape with rfl | rfl <;> omega
    rw [Finset.card_insert_of_notMem (by simp [hda, hdb, hdc])]
    rw [Finset.card_insert_of_notMem (by simp [hab, hac])]
    rw [Finset.card_insert_of_notMem (by simp [hbc])]
    simp
  have hle := Finset.card_le_card hsubset
  rw [hcard] at hle
  exact hle

/-- Prioritized complement-pair alternative for a subset of an interval with at most three
holes. If the target and each earlier pair fail, those failures are retained explicitly. -/
theorem dense_three_hole_exact_complement_priority
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3) :
    d ∈ remaining ∨
      (d ∉ remaining ∧ (1 ∈ remaining ∧ d - 1 ∈ remaining)) ∨
      (d ∉ remaining ∧ ¬(1 ∈ remaining ∧ d - 1 ∈ remaining) ∧
        (2 ∈ remaining ∧ d - 2 ∈ remaining)) ∨
      (d ∉ remaining ∧ ¬(1 ∈ remaining ∧ d - 1 ∈ remaining) ∧
        ¬(2 ∈ remaining ∧ d - 2 ∈ remaining) ∧
        (3 ∈ remaining ∧ d - 3 ∈ remaining)) := by
  by_cases hdRemaining : d ∈ remaining
  · exact Or.inl hdRemaining
  right
  by_cases hpOne : 1 ∈ remaining ∧ d - 1 ∈ remaining
  · exact Or.inl ⟨hdRemaining, hpOne⟩
  right
  by_cases hpTwo : 2 ∈ remaining ∧ d - 2 ∈ remaining
  · exact Or.inl ⟨hdRemaining, hpOne, hpTwo⟩
  right
  by_cases hpThree : 3 ∈ remaining ∧ d - 3 ∈ remaining
  · exact ⟨hdRemaining, hpOne, hpTwo, hpThree⟩
  let a := if 1 ∈ remaining then d - 1 else 1
  let b := if 2 ∈ remaining then d - 2 else 2
  let c := if 3 ∈ remaining then d - 3 else 3
  have haShape : a = 1 ∨ a = d - 1 := by
    simp only [a]
    split <;> simp_all
  have hbShape : b = 2 ∨ b = d - 2 := by
    simp only [b]
    split <;> simp_all
  have hcShape : c = 3 ∨ c = d - 3 := by
    simp only [c]
    split <;> simp_all
  have haMissing : a ∉ remaining := by
    simp only [a]
    split
    · rename_i hOne
      intro hPred
      exact hpOne ⟨hOne, hPred⟩
    · assumption
  have hbMissing : b ∉ remaining := by
    simp only [b]
    split
    · rename_i hTwo
      intro hPred
      exact hpTwo ⟨hTwo, hPred⟩
    · assumption
  have hcMissing : c ∉ remaining := by
    simp only [c]
    split
    · rename_i hThree
      intro hPred
      exact hpThree ⟨hThree, hPred⟩
    · assumption
  have hfour := four_holes_of_three_blocked_pairs N d remaining a b c hd hdN
    haShape hbShape hcShape hdRemaining haMissing hbMissing hcMissing
  omega

/-- A subset of an interval with at most three holes contains either its target counter or one
of the three disjoint complementary pairs nearest the ends of `Icc 1 d`. -/
theorem dense_three_hole_exact_complement_alternative
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3) :
    d ∈ remaining ∨
      (1 ∈ remaining ∧ d - 1 ∈ remaining) ∨
      (2 ∈ remaining ∧ d - 2 ∈ remaining) ∨
      (3 ∈ remaining ∧ d - 3 ∈ remaining) := by
  rcases dense_three_hole_exact_complement_priority N d remaining hd hdN hholes with
    hdRemaining | ⟨_, hpOne⟩ | ⟨_, _, hpTwo⟩ | ⟨_, _, _, hpThree⟩
  · exact Or.inl hdRemaining
  · exact Or.inr (Or.inl hpOne)
  · exact Or.inr (Or.inr (Or.inl hpTwo))
  · exact Or.inr (Or.inr (Or.inr hpThree))

/-- A losing dense position at deficit at least seven produces an exact-deficit block of at most
two counters whose residual tied game has a winning opening at least `d - 2`. The opening cannot
equal the old deficit. -/
theorem dense_loss_forces_near_or_upper_exact_residual_winner
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hsub : remaining ⊆ Finset.Icc 1 N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3)
    (hloss : (⟨remaining, d⟩ : Position).value = .loss) :
    ∃ block, ∃ hblock : block.Nonempty, ∃ w,
      block.card ≤ 2 ∧ block ⊆ remaining ∧ block.sum (fun x => x) = d ∧
      w ∈ remaining \ block ∧ (afterOpening (remaining \ block) w).value = .loss ∧
      block.max' hblock < w ∧ d - 2 ≤ w ∧ w ≠ d ∧ w ≤ N ∧
      (d < w ∨
        (w = d - 1 ∧ d ∉ remaining ∧ 1 ∉ remaining) ∨
        (w = d - 2 ∧ d ∉ remaining ∧ 2 ∉ remaining ∧
          (1 ∉ remaining ∨ d - 1 ∉ remaining))) := by
  by_cases hdRemaining : d ∈ remaining
  · let block : Finset ℕ := {d}
    have hblock : block.Nonempty := by simp [block]
    have hpositive : ∀ x ∈ block, 1 ≤ x := by
      intro x hx
      simp [block] at hx
      omega
    have hblockSub : block ⊆ remaining := by simpa [block] using hdRemaining
    have hsum : block.sum (fun x => x) = d := by simp [block]
    obtain ⟨w, hw, hwin, hgt⟩ :=
      Position.exists_winning_opening_gt_max_of_loss_of_exact_sum
        remaining block d hblock hpositive hblockSub hsum hloss
    have hmax : block.max' hblock = d := by simp [block]
    refine ⟨block, hblock, w, by simp [block], hblockSub, hsum, hw, hwin, hgt, ?_, ?_, ?_, ?_⟩
    · omega
    · exact fun hwd => (Finset.mem_sdiff.mp hw).2 (by simp [block, hwd])
    · exact (Finset.mem_Icc.mp (hsub (Finset.mem_sdiff.mp hw).1)).2
    · exact Or.inl (by omega)
  · rcases dense_three_hole_exact_complement_priority N d remaining hd hdN hholes with
      hdRemaining' | ⟨_, hpOne⟩ | ⟨_, hnoOne, hpTwo⟩ | ⟨_, hnoOne, hnoTwo, hpThree⟩
    · exact (hdRemaining hdRemaining').elim
    · let block : Finset ℕ := {1, d - 1}
      have hblock : block.Nonempty := by simp [block]
      have hpositive : ∀ x ∈ block, 1 ≤ x := by
        intro x hx
        simp only [block, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
      have hblockSub : block ⊆ remaining := by
        intro x hx
        simp only [block, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpOne.1
        · exact hpOne.2
      have hne : 1 ≠ d - 1 := by omega
      have hsum : block.sum (fun x => x) = d := by
        rw [show block = {1, d - 1} by rfl, Finset.sum_pair hne]
        omega
      obtain ⟨w, hw, hwin, hgt⟩ :=
        Position.exists_winning_opening_gt_max_of_loss_of_exact_sum
          remaining block d hblock hpositive hblockSub hsum hloss
      have hmax : block.max' hblock = d - 1 := by
        simp [block]
        omega
      have hgtNumeric := hgt
      rw [hmax] at hgtNumeric
      have hwNeD : w ≠ d := by
        intro hwd
        apply hdRemaining
        rw [← hwd]
        exact (Finset.mem_sdiff.mp hw).1
      refine ⟨block, hblock, w, Finset.card_le_two, hblockSub, hsum, hw, hwin, hgt, ?_, ?_, ?_, ?_⟩
      · omega
      · exact hwNeD
      · exact (Finset.mem_Icc.mp (hsub (Finset.mem_sdiff.mp hw).1)).2
      · exact Or.inl (by omega)
    · let block : Finset ℕ := {2, d - 2}
      have hblock : block.Nonempty := by simp [block]
      have hpositive : ∀ x ∈ block, 1 ≤ x := by
        intro x hx
        simp only [block, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
      have hblockSub : block ⊆ remaining := by
        intro x hx
        simp only [block, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpTwo.1
        · exact hpTwo.2
      have hne : 2 ≠ d - 2 := by omega
      have hsum : block.sum (fun x => x) = d := by
        rw [show block = {2, d - 2} by rfl, Finset.sum_pair hne]
        omega
      obtain ⟨w, hw, hwin, hgt⟩ :=
        Position.exists_winning_opening_gt_max_of_loss_of_exact_sum
          remaining block d hblock hpositive hblockSub hsum hloss
      have hmax : block.max' hblock = d - 2 := by
        simp [block]
        omega
      have hgtNumeric := hgt
      rw [hmax] at hgtNumeric
      have hwNeD : w ≠ d := by
        intro hwd
        apply hdRemaining
        rw [← hwd]
        exact (Finset.mem_sdiff.mp hw).1
      refine ⟨block, hblock, w, Finset.card_le_two, hblockSub, hsum, hw, hwin, hgt, ?_, ?_, ?_, ?_⟩
      · omega
      · exact hwNeD
      · exact (Finset.mem_Icc.mp (hsub (Finset.mem_sdiff.mp hw).1)).2
      · by_cases hupper : d < w
        · exact Or.inl hupper
        · right
          left
          have hwEq : w = d - 1 := by omega
          refine ⟨hwEq, hdRemaining, ?_⟩
          intro hOne
          apply hnoOne
          refine ⟨hOne, ?_⟩
          rw [← hwEq]
          exact (Finset.mem_sdiff.mp hw).1
    · let block : Finset ℕ := {3, d - 3}
      have hblock : block.Nonempty := by simp [block]
      have hpositive : ∀ x ∈ block, 1 ≤ x := by
        intro x hx
        simp only [block, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
      have hblockSub : block ⊆ remaining := by
        intro x hx
        simp only [block, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hpThree.1
        · exact hpThree.2
      have hne : 3 ≠ d - 3 := by omega
      have hsum : block.sum (fun x => x) = d := by
        rw [show block = {3, d - 3} by rfl, Finset.sum_pair hne]
        omega
      obtain ⟨w, hw, hwin, hgt⟩ :=
        Position.exists_winning_opening_gt_max_of_loss_of_exact_sum
          remaining block d hblock hpositive hblockSub hsum hloss
      have hmax : block.max' hblock = d - 3 := by
        simp [block]
        omega
      have hgtNumeric := hgt
      rw [hmax] at hgtNumeric
      have hwNeD : w ≠ d := by
        intro hwd
        apply hdRemaining
        rw [← hwd]
        exact (Finset.mem_sdiff.mp hw).1
      refine ⟨block, hblock, w, Finset.card_le_two, hblockSub, hsum, hw, hwin, hgt, ?_, ?_, ?_, ?_⟩
      · omega
      · exact hwNeD
      · exact (Finset.mem_Icc.mp (hsub (Finset.mem_sdiff.mp hw).1)).2
      · by_cases hupper : d < w
        · exact Or.inl hupper
        · by_cases hnearOne : w = d - 1
          · right
            left
            refine ⟨hnearOne, hdRemaining, ?_⟩
            intro hOne
            apply hnoOne
            refine ⟨hOne, ?_⟩
            rw [← hnearOne]
            exact (Finset.mem_sdiff.mp hw).1
          · right
            right
            have hnearTwo : w = d - 2 := by omega
            refine ⟨hnearTwo, hdRemaining, ?_, ?_⟩
            · intro hTwo
              apply hnoTwo
              refine ⟨hTwo, ?_⟩
              rw [← hnearTwo]
              exact (Finset.mem_sdiff.mp hw).1
            · by_cases hOne : 1 ∈ remaining
              · right
                intro hPred
                exact hnoOne ⟨hOne, hPred⟩
              · exact Or.inl hOne

/-- The only non-increasing alternatives in the dense exact-sum obstruction immediately descend
to a prefix-blocked loss. At deficit two, if counter one is still present, taking it once more
produces a deficit-one loss with counter one erased. -/
theorem dense_loss_forces_upper_residual_or_small_prefix_blocked_loss
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hsub : remaining ⊆ Finset.Icc 1 N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3)
    (hloss : (⟨remaining, d⟩ : Position).value = .loss) :
    (∃ block, ∃ hblock : block.Nonempty, ∃ w,
      block.card ≤ 2 ∧ block ⊆ remaining ∧ block.sum (fun x => x) = d ∧
      w ∈ remaining \ block ∧ (afterOpening (remaining \ block) w).value = .loss ∧
      block.max' hblock < w ∧ d < w ∧ w ≤ N) ∨
    (d ∉ remaining ∧ 1 ∉ remaining ∧ d - 1 ∈ remaining ∧
      (⟨remaining.erase (d - 1), 1⟩ : Position).value = .loss) ∨
    (d ∉ remaining ∧ 1 ∉ remaining ∧ 2 ∉ remaining ∧ d - 2 ∈ remaining ∧
      (⟨remaining.erase (d - 2), 2⟩ : Position).value = .loss) ∨
    (d ∉ remaining ∧ 1 ∈ remaining ∧ 2 ∉ remaining ∧
      d - 1 ∉ remaining ∧ d - 2 ∈ remaining ∧
      (⟨(remaining.erase (d - 2)).erase 1, 1⟩ : Position).value = .loss) := by
  obtain ⟨block, hblock, w, hcard, hblockSub, hsum, hw, hwin, hgt,
      hwLower, hwNe, hwN, hclass⟩ :=
    dense_loss_forces_near_or_upper_exact_residual_winner
      N d remaining hd hdN hsub hholes hloss
  have hsumLe : d ≤ remaining.sum (fun x => x) := by
    have hle := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hblockSub
    change block.sum (fun x => x) ≤ remaining.sum (fun x => x) at hle
    rw [hsum] at hle
    exact hle
  have hcatch : ¬ remaining.sum (fun x => x) < d := by omega
  rcases hclass with hupper | hnearOne | hnearTwo
  · left
    exact ⟨block, hblock, w, hcard, hblockSub, hsum, hw, hwin, hgt, hupper, hwN⟩
  · right
    left
    rcases hnearOne with ⟨hwEq, hdMissing, hOneMissing⟩
    have hPredRemaining : d - 1 ∈ remaining := by
      rw [← hwEq]
      exact (Finset.mem_sdiff.mp hw).1
    refine ⟨hdMissing, hOneMissing, hPredRemaining, ?_⟩
    have hchild := Position.loss_after_continuing_pick_of_value_eq_loss
      (⟨remaining, d⟩ : Position) (Finset.mem_sdiff.mp hw).1 hcatch
        (show w < d by omega) hloss
    have hsubOne : d - (d - 1) = 1 := by omega
    simpa [Position.afterPick, hwEq, show 0 < d by omega, hsubOne] using hchild
  · right
    rcases hnearTwo with ⟨hwEq, hdMissing, hTwoMissing, hfirstPairBlocked⟩
    have hNearRemaining : d - 2 ∈ remaining := by
      rw [← hwEq]
      exact (Finset.mem_sdiff.mp hw).1
    have hchild := Position.loss_after_continuing_pick_of_value_eq_loss
      (⟨remaining, d⟩ : Position) (Finset.mem_sdiff.mp hw).1 hcatch
        (show w < d by omega) hloss
    have hsubTwo : d - (d - 2) = 2 := by omega
    have hdeficitTwoLoss :
        (⟨remaining.erase (d - 2), 2⟩ : Position).value = .loss := by
      simpa [Position.afterPick, hwEq, show 0 < d by omega, hsubTwo] using hchild
    by_cases hOne : 1 ∈ remaining
    · right
      right
      have hPredMissing : d - 1 ∉ remaining := by
        rcases hfirstPairBlocked with hOneMissing | hPredMissing
        · exact (hOneMissing hOne).elim
        · exact hPredMissing
      have hThree : 3 ∈ remaining := by
        rcases dense_three_hole_exact_complement_priority N d remaining hd hdN hholes with
          hdRemaining | ⟨_, hpOne⟩ | ⟨_, _, hpTwo⟩ | ⟨_, _, _, hpThree⟩
        · exact (hdMissing hdRemaining).elim
        · exact (hPredMissing hpOne.2).elim
        · exact (hTwoMissing hpTwo.1).elim
        · exact hpThree.1
      have hOneChild : 1 ∈ remaining.erase (d - 2) := by
        apply Finset.mem_erase.mpr
        exact ⟨by omega, hOne⟩
      have hThreeChild : 3 ∈ remaining.erase (d - 2) := by
        apply Finset.mem_erase.mpr
        exact ⟨by omega, hThree⟩
      have hThreeLeSum :
          3 ≤ (remaining.erase (d - 2)).sum (fun x => x) := by
        have hsingleton : ({3} : Finset ℕ) ⊆ remaining.erase (d - 2) := by
          simpa using hThreeChild
        have hle := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsingleton
        simpa using hle
      have hchildCatch :
          ¬ (remaining.erase (d - 2)).sum (fun x => x) < 2 := by
        omega
      have hgrandchild := Position.loss_after_continuing_pick_of_value_eq_loss
        (⟨remaining.erase (d - 2), 2⟩ : Position) hOneChild hchildCatch
          (show 1 < 2 by omega) hdeficitTwoLoss
      refine ⟨hdMissing, hOne, hTwoMissing, hPredMissing, hNearRemaining, ?_⟩
      simpa [Position.afterPick] using hgrandchild
    · right
      left
      exact ⟨hdMissing, hOne, hTwoMissing, hNearRemaining, hdeficitTwoLoss⟩

end CatchUp

