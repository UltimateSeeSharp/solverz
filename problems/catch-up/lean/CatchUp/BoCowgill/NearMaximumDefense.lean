/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/NearMaximumDefense.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DeficitCrossing
public import CatchUp.BoCowgill.DeficitTwo

/-!
# NearMaximumDefense

A complementary-pair defense rules out loss at deficit b under a near-maximum bound and explicit
minimum/pair hypotheses.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.NearMaximumDefense
open CatchUp.DeficitTwo (all_catching)

/-!
# A complementary-pair defense near the largest counter

A hypothetical loss with the exact counter b and complementary counters a and
b-a forces a genuine residual winning opening above b+a. The proof covers every
legal reply, including taking the reserved counter b. Thus an upper label bound
b+a rules out loss. No parity, interval, or bounded-cardinality hypothesis is used.
-/

/-- The complementary pair is a legal midpoint turn from the lower deficit. -/
theorem midpoint_pair_nonloss (C : Finset ℕ) (a b c : ℕ)
    (hc : 0 < c) (hca : c ≤ a) (hab : 2 * a < b)
    (haC : a ∈ C) (hbaC : b - a ∈ C)
    (hhigh : (⟨C, b + c⟩ : Position).value = .loss) :
    (⟨C, b - c⟩ : Position).value ≠ .loss := by
  have hne : a ≠ b - a := by omega
  have hsum : ({a, b - a} : Finset ℕ).sum (fun x ↦ x) = b := by
    simp only [Finset.sum_pair hne]
    omega
  apply DeficitCrossing.nonloss_of_loss_and_midpoint_turn C {a, b - a}
    (b + c) (b - c) (b - a) hhigh
  · refine ⟨?_, ?_, ?_, Or.inr ?_⟩
    · simp
    · simpa only [insert_subset_iff, singleton_subset_iff] using And.intro haC hbaC
    · simpa only [hsum] using Nat.sub_le b c
    · simp only [erase_insert_of_ne hne, erase_singleton, insert_empty_eq, sum_singleton]
      omega
  all_goals omega

/-- Every legal pick catches immediately; the reserve-taking branch uses the midpoint turn. -/
theorem reserve_nonwin_of_midpoint (C : Finset ℕ) (a b c : ℕ)
    (hc : 0 < c) (hca : c ≤ a) (hab : 2 * a < b)
    (haC : a ∈ C) (hbaC : b - a ∈ C)
    (hmin : ∀ x ∈ C, a ≤ x) (hb : b ∉ C) (hbc : b + c ∉ C)
    (hhigh : (⟨C, b + c⟩ : Position).value = .loss) :
    (⟨insert b C, c⟩ : Position).value ≠ .win := by
  apply all_catching (insert b C) c (by simp)
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · exact hca.trans (hmin x hx)
  · intro x hx
    by_cases hxb : x = b
    · simpa only [hxb, erase_insert hb] using
        midpoint_pair_nonloss C a b c hc hca hab haC hbaC hhigh
    · have hxC : x ∈ C := (mem_insert.mp hx).resolve_left hxb
      have turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ {x} x :=
        ⟨by simp, singleton_subset_iff.mpr hx, by simpa using hca.trans (hmin x hxC),
          Or.inl rfl⟩
      have hbY : b ∉ ({x} : Finset ℕ) := by simpa using Ne.symm hxb
      have hne : ({x} : Finset ℕ).sum (fun y ↦ y) ≠ b + c := by
        simpa using (show x ≠ b + c from fun he ↦ hbc (he ▸ hxC))
      have hwin := PairEntranceShadow.endpoint_win_of_total_ne C {x} b c x
        hb hhigh turn hbY hne
      have hwin' : (⟨(insert b C).erase x, x - c⟩ : Position).value = .win := by
        simpa [sdiff_singleton_eq_erase, erase_insert_of_ne (Ne.symm hxb)] using hwin
      rw [hwin']
      decide

/-- A genuine residual winning opening above b cannot lie in the band (b,b+a]. -/
theorem winning_opening_gt_bound (S : Finset ℕ) (a b w : ℕ) (ha : 0 < a)
    (hmin : ∀ x ∈ S, a ≤ x) (haS : a ∈ S) (hbaS : b - a ∈ S) (hbS : b ∈ S)
    (hab : 2 * a < b) (hloss : (⟨S, b⟩ : Position).value = .loss)
    (hw : w ∈ S \ {b}) (hbw : b < w)
    (hshadow : (afterOpening (S \ {b}) w).value = .loss) :
    b + a < w := by
  by_contra hupper
  have hwS : w ∈ S := (mem_sdiff.mp hw).1
  have hwupper : w ≤ b + a := Nat.le_of_not_gt hupper
  let c := w - b
  have hc : 0 < c := by dsimp [c]; omega
  have hca : c ≤ a := by dsimp [c]; omega
  have hbcw : b + c = w := by dsimp [c]; omega
  let C := (S.erase b).erase w
  have haC : a ∈ C := by
    simp [C, show a ≠ w by omega, show a ≠ b by omega, haS]
  have hbaC : b - a ∈ C := by
    simp [C, show b - a ≠ w by omega, show b - a ≠ b by omega, hbaS]
  have hminC : ∀ x ∈ C, a ≤ x :=
    fun x hx ↦ hmin x (mem_erase.mp (mem_erase.mp hx).2).2
  have hbC : b ∉ C := by simp [C]
  have hbcC : b + c ∉ C := by simp [C, hbcw]
  have hhigh : (⟨C, b + c⟩ : Position).value = .loss := by
    simpa only [C, hbcw, afterOpening, sdiff_singleton_eq_erase] using hshadow
  have hbErase : b ∈ S.erase w := mem_erase.mpr ⟨Nat.ne_of_lt hbw, hbS⟩
  have hset : S.erase w = insert b C := by
    simpa only [C, erase_right_comm] using (Finset.insert_erase hbErase).symm
  have turn : TurnSet ⟨⟨S, b⟩, .p1⟩ {w} w :=
    ⟨by simp, singleton_subset_iff.mpr hwS, by simpa using Nat.le_of_lt hbw, Or.inl rfl⟩
  have hendpoint := PairEntranceShadow.turn_endpoint_win_of_loss ⟨S, b⟩ {w} w turn hloss
  have hwin : (⟨insert b C, c⟩ : Position).value = .win := by
    simpa [completedTurnEndpoint, sdiff_singleton_eq_erase, hset, c] using hendpoint
  exact reserve_nonwin_of_midpoint C a b c hc hca hab haC hbaC hminC hbC hbcC hhigh hwin

/-- A hypothetical loss forces a genuine residual winning opening strictly above b+a. -/
theorem exists_winning_opening_gt_bound (S : Finset ℕ) (a b : ℕ) (ha : 0 < a)
    (hmin : ∀ x ∈ S, a ≤ x) (haS : a ∈ S) (hbaS : b - a ∈ S) (hbS : b ∈ S)
    (hab : 2 * a < b) (hloss : (⟨S, b⟩ : Position).value = .loss) :
    ∃ w ∈ S \ {b}, (afterOpening (S \ {b}) w).value = .loss ∧ b + a < w := by
  obtain ⟨w, hw, hshadow, hgt⟩ :=
    Position.exists_winning_opening_gt_max_of_loss_of_exact_sum S {b} b
      (by simp) (by simpa using (show 1 ≤ b by omega))
      (by simpa only [singleton_subset_iff] using hbS) (by simp) hloss
  exact ⟨w, hw, hshadow, winning_opening_gt_bound S a b w ha hmin haS hbaS hbS
    hab hloss hw (by simpa using hgt) hshadow⟩

/-- Complementary counters and a bounded label range rule out loss, uniformly in the support. -/
theorem value_ne_loss (S : Finset ℕ) (a b : ℕ) (ha : 0 < a)
    (hmin : ∀ x ∈ S, a ≤ x) (haS : a ∈ S) (hbaS : b - a ∈ S) (hbS : b ∈ S)
    (hab : 2 * a < b) (hmax : ∀ x ∈ S, x ≤ b + a) :
    (⟨S, b⟩ : Position).value ≠ .loss := by
  intro hloss
  obtain ⟨w, hw, _, hgt⟩ :=
    exists_winning_opening_gt_bound S a b ha hmin haS hbaS hbS hab hloss
  exact (not_lt_of_ge (hmax w (mem_sdiff.mp hw).1)) hgt

end CatchUp.NearMaximumDefense

