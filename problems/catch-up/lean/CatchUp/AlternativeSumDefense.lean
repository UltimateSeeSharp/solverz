/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/AlternativeSumDefense.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.DeficitCrossing
public import CatchUp.DeficitTwo

/-!
# An alternative exact-sum block defends a near-maximum deficit

If counter `b` is available and a separate block also sums to `b`, a hypothetical
loss at deficit `b` forces a genuine residual winning opening above `b+a`, where
`a>0` is any lower bound on the counters. Thus an upper bound `b+a` rules out loss.

The block can have arbitrary cardinality. A sufficiently large member can end a
legal midpoint turn, replacing the complementary pair used previously.
Every opponent reply is retained; neither parity nor interval structure is needed.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.AlternativeSumDefense
open CatchUp.DeficitTwo (all_catching)

/-- Any exact-sum block with a sufficiently large final counter is a midpoint turn. -/
theorem midpoint_block_nonloss (C B : Finset ℕ) (b c final : ℕ)
    (hBC : B ⊆ C) (hf : final ∈ B) (hc : 0 < c) (hcf : c < final)
    (hsum : B.sum (fun x ↦ x) = b)
    (hhigh : (⟨C,b+c⟩ : Position).value = .loss) :
    (⟨C,b-c⟩ : Position).value ≠ .loss := by
  exact DeficitCrossing.nonloss_of_loss_and_midpoint_turn C B (b+c) (b-c) final hhigh
    ⟨hf,hBC,by simpa only [hsum] using Nat.sub_le b c,Or.inr (by
      have hp := sum_erase_add B (fun x : ℕ ↦ x) hf
      rw [hsum] at hp
      change (B.erase final).sum (fun x ↦ x) + final = b at hp
      change (B.erase final).sum (fun x ↦ x) < b-c
      omega)⟩
    (by omega)
    (by
      have hfb := single_le_sum (f := fun x : ℕ ↦ x) (fun _ _ ↦ Nat.zero_le _) hf
      rw [hsum] at hfb
      change final ≤ b at hfb
      omega)

/-- All legal replies catch; taking the reserve is defended by the alternative block. -/
theorem reserve_nonwin_of_block (C B : Finset ℕ) (a b c final : ℕ)
    (hc : 0 < c) (hca : c ≤ a) (hf : final ∈ B) (hcf : c < final)
    (hBC : B ⊆ C) (hsum : B.sum (fun x ↦ x) = b)
    (hmin : ∀ x ∈ C, a ≤ x) (hb : b ∉ C) (hbc : b+c ∉ C)
    (hhigh : (⟨C,b+c⟩ : Position).value = .loss) :
    (⟨insert b C,c⟩ : Position).value ≠ .win := by
  have hfb : final ≤ b := by
    simpa only [hsum] using single_le_sum (f := fun x : ℕ ↦ x) (fun _ _ ↦ Nat.zero_le _) hf
  apply all_catching (insert b C) c (by simp)
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · exact hca.trans (hmin x hx)
  · intro x hx
    by_cases hxb : x = b
    · simpa only [hxb, erase_insert hb] using
        midpoint_block_nonloss C B b c final hBC hf hc hcf hsum hhigh
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

private theorem exists_large_member (S B : Finset ℕ) (a b : ℕ)
    (ha : 0 < a) (hmin : ∀ x ∈ S, a ≤ x) (hbS : b ∈ S)
    (hBS : B ⊆ S \ {b}) (hsum : B.sum (fun x ↦ x) = b) :
    ∃ final ∈ B, a < final := by
  have hbnot : b ∉ B := by
    intro hb
    exact (mem_sdiff.mp (hBS hb)).2 (by simp)
  have hBN : B.Nonempty := by
    by_contra hn
    have he := not_nonempty_iff_eq_empty.mp hn
    have hba := hmin b hbS
    simp only [he,sum_empty] at hsum
    omega
  by_contra hn
  push Not at hn
  have heach : ∀ x ∈ B, x=a := by
    intro x hx
    exact Nat.le_antisymm (hn x hx) (hmin x (mem_sdiff.mp (hBS hx)).1)
  obtain ⟨x,hx⟩ := hBN
  have haB : a ∈ B := heach x hx ▸ hx
  have heq : B={a} := eq_singleton_iff_unique_mem.mpr ⟨haB,heach⟩
  rw [heq,sum_singleton] at hsum
  exact hbnot (hsum ▸ haB)

/-- Every genuine residual winning opening above b lies above b+a. -/
theorem winning_opening_gt_bound (S B : Finset ℕ) (a b w : ℕ)
    (ha : 0 < a) (hmin : ∀ x ∈ S, a ≤ x) (hbS : b ∈ S)
    (hBS : B ⊆ S \ {b}) (hsum : B.sum (fun x ↦ x) = b)
    (hloss : (⟨S,b⟩ : Position).value = .loss)
    (hw : w ∈ S \ {b}) (hbw : b < w)
    (hshadow : (afterOpening (S \ {b}) w).value = .loss) :
    b+a < w := by
  by_contra hupper
  have hwS : w ∈ S := (mem_sdiff.mp hw).1
  have hwupper : w ≤ b + a := Nat.le_of_not_gt hupper
  let c := w - b
  have hc : 0 < c := by dsimp [c]; omega
  have hca : c ≤ a := by dsimp [c]; omega
  have hbcw : b + c = w := by dsimp [c]; omega
  let C := (S.erase b).erase w
  obtain ⟨final,hf,haf⟩ := exists_large_member S B a b ha hmin hbS hBS hsum
  have hBC : B ⊆ C := by
    intro x hx
    have hxs := mem_sdiff.mp (hBS hx)
    have hxb : x ≤ b := by
      simpa only [hsum] using single_le_sum (f := fun x : ℕ ↦ x) (fun _ _ ↦ Nat.zero_le _) hx
    exact mem_erase.mpr ⟨by omega,mem_erase.mpr ⟨by simpa using hxs.2,hxs.1⟩⟩
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
  exact reserve_nonwin_of_block C B a b c final hc hca hf (by omega) hBC hsum
    hminC hbC hbcC hhigh hwin

/-- A hypothetical loss forces a genuine residual winning opening above b+a. -/
theorem exists_winning_opening_gt_bound (S B : Finset ℕ) (a b : ℕ)
    (ha : 0 < a) (hmin : ∀ x ∈ S, a ≤ x) (hbS : b ∈ S)
    (hBS : B ⊆ S \ {b}) (hsum : B.sum (fun x ↦ x) = b)
    (hloss : (⟨S,b⟩ : Position).value = .loss) :
    ∃ w ∈ S \ {b}, (afterOpening (S \ {b}) w).value = .loss ∧ b+a < w := by
  have hba := hmin b hbS
  obtain ⟨w,hw,hshadow,hgt⟩ :=
    Position.exists_winning_opening_gt_max_of_loss_of_exact_sum S {b} b
      (by simp) (by simpa using (show 1 ≤ b by omega))
      (by simpa only [singleton_subset_iff] using hbS) (by simp) hloss
  exact ⟨w,hw,hshadow,winning_opening_gt_bound S B a b w ha hmin hbS hBS hsum
    hloss hw (by simpa using hgt) hshadow⟩

/-- An alternative exact-sum block rules out loss when all labels are at most b+a. -/
theorem value_ne_loss (S B : Finset ℕ) (a b : ℕ)
    (ha : 0 < a) (hmin : ∀ x ∈ S, a ≤ x) (hbS : b ∈ S)
    (hBS : B ⊆ S \ {b}) (hsum : B.sum (fun x ↦ x) = b)
    (hmax : ∀ x ∈ S, x ≤ b+a) :
    (⟨S,b⟩ : Position).value ≠ .loss := by
  intro hloss
  obtain ⟨w,hw,_,hgt⟩ :=
    exists_winning_opening_gt_bound S B a b ha hmin hbS hBS hsum hloss
  exact (not_lt_of_ge (hmax w (mem_sdiff.mp hw).1)) hgt

end CatchUp.AlternativeSumDefense

