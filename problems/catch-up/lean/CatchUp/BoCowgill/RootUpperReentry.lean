/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/RootUpperReentry.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DeficitCrossing

/-!
# Excluding the seven-opening upper branch

A losing shadow at deficit seven makes the reserve-five endpoint nonwinning.
The proof retains every legal opponent turn, including taking the reserve.
A genuine parent loss therefore cannot have this losing seven-shadow.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.RootUpperReentry

private theorem turn_set_singleton_at_two
    (C Y : Finset ℕ) (final : ℕ) (hmin : ∀ x ∈ C, 2 ≤ x)
    (turn : TurnSet ⟨⟨C, 2⟩, .p1⟩ Y final) : Y = {final} := by
  rcases turn.preparation_below with hsingle | hbelow
  · exact hsingle
  · apply eq_singleton_iff_unique_mem.mpr
    refine ⟨turn.final_mem, ?_⟩
    intro x hx
    by_contra hne
    have hlow := hmin x (turn.chosen_subset hx)
    have hsum := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y)
      (Finset.mem_erase.mpr ⟨hne, hx⟩)
    change (Y.erase final).sum (fun x ↦ x) < 2 at hbelow
    omega

/-- All opponent turns are safe, including the reserve-taking singleton five. -/
theorem reserve_five_nonwin_of_seven_loss
    (C : Finset ℕ) (h2 : 2 ∈ C) (h3 : 3 ∈ C)
    (hmin : ∀ x ∈ C, 2 ≤ x) (h5 : 5 ∉ C) (h7 : 7 ∉ C)
    (hhigh : (⟨C, 7⟩ : Position).value = .loss) :
    (⟨insert 5 C, 2⟩ : Position).value ≠ .win := by
  have hcatch : ¬ (insert 5 C).sum (fun x ↦ x) < 2 := by
    have hsum := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y)
      (show 5 ∈ insert 5 C by simp)
    omega
  apply (Position.value_ne_win_iff_forall_turn_sets ⟨insert 5 C, 2⟩
    (by simp) hcatch).mpr
  intro Y final turn
  have hminInsert : ∀ x ∈ insert 5 C, 2 ≤ x := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · exact hmin x hx
  have hsingle := turn_set_singleton_at_two (insert 5 C) Y final hminInsert turn
  subst Y
  by_cases he : final = 5
  · subst final
    simpa [completedTurnEndpoint, sdiff_singleton_eq_erase, h5] using
      DeficitCrossing.seven_to_three C h2 h3 hhigh
  · have hfinalC : final ∈ C := by
      have hm := turn.chosen_subset turn.final_mem
      change final ∈ insert 5 C at hm
      exact (mem_insert.mp hm).resolve_left he
    have hbY : 5 ∉ ({final} : Finset ℕ) := by simpa using Ne.symm he
    have hne : ({final} : Finset ℕ).sum (fun x ↦ x) ≠ 5 + 2 := by
      simpa using (show final ≠ 7 from fun hf ↦ h7 (hf ▸ hfinalC))
    have hwin := PairEntranceShadow.endpoint_win_of_total_ne C {final} 5 2 final
      h5 hhigh turn hbY hne
    rw [PairEntranceShadow.reserve_endpoint_eq C {final} 5 2 hbY, hwin]
    decide

/-- A parent loss cannot coexist with the losing seven-shadow: its pick seven would win. -/
theorem seven_shadow_nonloss_of_parent_loss
    (C : Finset ℕ) (h2 : 2 ∈ C) (h3 : 3 ∈ C)
    (hmin : ∀ x ∈ C, 2 ≤ x) (h5 : 5 ∉ C) (h7 : 7 ∉ C)
    (hparent : (⟨insert 5 (insert 7 C), 5⟩ : Position).value = .loss) :
    (⟨C, 7⟩ : Position).value ≠ .loss := by
  intro hhigh
  have turn : TurnSet ⟨⟨insert 5 (insert 7 C), 5⟩, .p1⟩ {7} 7 := by
    refine ⟨by simp, by simp, by norm_num, Or.inl rfl⟩
  have hwin := PairEntranceShadow.turn_endpoint_win_of_loss
    ⟨insert 5 (insert 7 C), 5⟩ {7} 7 turn hparent
  have hQwin : (⟨insert 5 C, 2⟩ : Position).value = .win := by
    simpa [completedTurnEndpoint, sdiff_singleton_eq_erase, erase_insert_of_ne, h7] using hwin
  exact reserve_five_nonwin_of_seven_loss C h2 h3 hmin h5 h7 hhigh hQwin

/-- The actual interval parent excludes a genuine residual winning opening seven. -/
theorem interval_seven_shadow_nonloss (N : ℕ) (hN : 7 ≤ N)
    (hparent : (⟨Icc 2 N \ {6}, 5⟩ : Position).value = .loss) :
    (⟨Icc 2 N \ {5, 6, 7}, 7⟩ : Position).value ≠ .loss := by
  let C := Icc 2 N \ {5, 6, 7}
  have h2 : 2 ∈ C := by simp [C]; omega
  have h3 : 3 ∈ C := by simp [C]; omega
  have hmin : ∀ x ∈ C, 2 ≤ x := by
    intro x hx
    exact (mem_Icc.mp (mem_sdiff.mp hx).1).1
  have h5 : 5 ∉ C := by simp [C]
  have h7 : 7 ∉ C := by simp [C]
  have hparentSet : insert 5 (insert 7 C) = Icc 2 N \ {6} := by
    ext x
    simp only [C, mem_insert, mem_sdiff, mem_Icc, mem_singleton]
    omega
  have hp : (⟨insert 5 (insert 7 C), 5⟩ : Position).value = .loss := by
    simpa only [hparentSet] using hparent
  exact seven_shadow_nonloss_of_parent_loss C h2 h3 hmin h5 h7 hp

/-- Every losing interval parent has a genuine residual winning opening at least eight.
This removes seven; the separate eight-opening reentry obligation remains open. -/
theorem interval_upper_opening_ge_eight (N : ℕ) (hN : 7 ≤ N)
    (hparent : (⟨Icc 2 N \ {6}, 5⟩ : Position).value = .loss) :
    ∃ w ∈ Icc 2 N \ {5, 6}, 8 ≤ w ∧
      (afterOpening (Icc 2 N \ {5, 6}) w).value = .loss := by
  let Q := Icc 2 N \ {6}
  have h5Q : 5 ∈ Q := by simp [Q]; omega
  obtain ⟨w, hw, hwin, hgt⟩ :=
    Position.exists_winning_opening_gt_max_of_loss_of_exact_sum Q {5} 5
      (by simp) (by intro x hx; simp only [mem_singleton] at hx; omega)
      (by simpa only [singleton_subset_iff] using h5Q) (by simp) hparent
  have hresidual : Q \ {5} = Icc 2 N \ {5, 6} := by
    ext x
    simp only [Q, mem_sdiff, mem_Icc, mem_insert, mem_singleton]
    tauto
  have hwin' : (afterOpening (Icc 2 N \ {5, 6}) w).value = .loss := by
    simpa only [hresidual] using hwin
  have hw' : w ∈ Icc 2 N \ {5, 6} := by simpa only [hresidual] using hw
  have hw5 : 5 < w := by simpa using hgt
  have hw6 : w ≠ 6 := by
    intro he
    subst w
    simp at hw'
  have hw7 : w ≠ 7 := by
    intro he
    subst w
    have hchild : (Icc 2 N \ {5, 6}).erase 7 = Icc 2 N \ {5, 6, 7} := by
      ext x
      simp only [mem_erase, mem_sdiff, mem_Icc, mem_insert, mem_singleton]
      tauto
    have hhigh : (⟨Icc 2 N \ {5, 6, 7}, 7⟩ : Position).value = .loss := by
      simpa only [afterOpening, hchild] using hwin'
    exact interval_seven_shadow_nonloss N hN hparent hhigh
  exact ⟨w, hw', by omega, hwin'⟩

end CatchUp.RootUpperReentry
