/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/EqualityReserveObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.PairEntranceShadow

/-!
# Equality excludes every completed repair turn containing the reserve

A repair is matched to a completed turn in the losing shadow, so it leaves
a win to the opponent. This excludes arbitrary multi-pick reserve repairs;
it does not rule out a repair avoiding the reserve or assert the equality
endpoint itself loses.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.EqualityReserveObstruction

/-- A complete turn at deficit b which contains b must finish with b. -/
theorem reserve_is_final
    (R Z : Finset ℕ) (b final : ℕ)
    (turn : TurnSet ⟨⟨R, b⟩, .p1⟩ Z final) (hbZ : b ∈ Z) : final = b := by
  rcases turn.preparation_below with hs | hp
  · rw [hs] at hbZ
    exact (mem_singleton.mp hbZ).symm
  · by_contra hne
    have hm : b ∈ Z.erase final := mem_erase.mpr ⟨Ne.symm hne, hbZ⟩
    have hsum := Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hm
    change b ≤ (Z.erase final).sum (fun x ↦ x) at hsum
    change (Z.erase final).sum (fun x ↦ x) < b at hp
    omega

/-- The equality opponent turn leaves the actual reserve position at deficit b. -/
theorem equality_endpoint_eq
    (C Y : Finset ℕ) (b c : ℕ) (hbY : b ∉ Y)
    (heq : Y.sum (fun x ↦ x) = b + c) :
    (completedTurnEndpoint ⟨⟨insert b C, c⟩, .p1⟩ Y).toPosition =
      ⟨insert b (C \ Y), b⟩ := by
  rw [PairEntranceShadow.reserve_endpoint_eq C Y b c hbY, heq]
  simp

/-- Every complete repair turn containing the reserve leaves a win to the opponent. -/
theorem repair_endpoint_win
    (C Y Z : Finset ℕ) (b c final repairFinal : ℕ) (hbpos : 0 < b) (hcpos : 0 < c)
    (hb : b ∉ C) (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final)
    (hbY : b ∉ Y) (heq : Y.sum (fun x ↦ x) = b + c)
    (repair : TurnSet ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z repairFinal) (hbZ : b ∈ Z) :
    (completedTurnEndpoint ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z).toPosition.value = .win := by
  let K := Z.erase b
  have hY : Y ⊆ C := by
    intro x hx
    have hm := turn.chosen_subset hx
    change x ∈ insert b C at hm
    rcases mem_insert.mp hm with he | hm
    · subst x
      exact False.elim (hbY hx)
    · exact hm
  have hK : K ⊆ C \ Y := by
    intro x hx
    have hn := (mem_erase.mp hx).1
    have hm := repair.chosen_subset (mem_of_mem_erase hx)
    change x ∈ insert b (C \ Y) at hm
    exact (mem_insert.mp hm).resolve_left hn
  have hfinal : repairFinal = b := reserve_is_final _ Z b repairFinal repair hbZ
  have hpK : K.sum (fun x ↦ x) < b := by
    rcases repair.preparation_below with hs | hp
    · rw [hfinal] at hs
      simpa [K, hs] using hbpos
    · simpa only [hfinal] using hp
  have hpY : (Y.erase final).sum (fun x ↦ x) < c := by
    rcases turn.preparation_below with hs | hp
    · simpa [hs] using hcpos
    · exact hp
  have hdisjoint : Disjoint Y K := Finset.disjoint_left.mpr (by
    intro x hxY hxK
    exact (mem_sdiff.mp (hK hxK)).2 hxY)
  have hsumQ : (Y ∪ K).sum (fun x ↦ x) = b + c + K.sum (fun x ↦ x) := by
    rw [Finset.sum_union hdisjoint, heq]
  have hYerase := Finset.sum_erase_add Y (fun x : ℕ ↦ x) turn.final_mem
  have hfQ : final ∈ Y ∪ K := mem_union.mpr (Or.inl turn.final_mem)
  have hQerase := Finset.sum_erase_add (Y ∪ K) (fun x : ℕ ↦ x) hfQ
  try simp only at hYerase hQerase
  rw [heq] at hYerase
  rw [hsumQ] at hQerase
  have hpQ : ((Y ∪ K).erase final).sum (fun x ↦ x) < b + c := by omega
  have hshadow : TurnSet ⟨⟨C, b + c⟩, .p1⟩ (Y ∪ K) final := by
    refine ⟨hfQ, ?_, ?_, Or.inr hpQ⟩
    · intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact hY hx
      · exact (mem_sdiff.mp (hK hx)).1
    · change b + c ≤ (Y ∪ K).sum (fun x ↦ x)
      rw [hsumQ]
      omega
  have hwin := PairEntranceShadow.turn_endpoint_win_of_loss ⟨C, b + c⟩ (Y ∪ K)
    final hshadow hloss
  change (⟨C \ (Y ∪ K), (Y ∪ K).sum (fun x ↦ x) - (b + c)⟩ : Position).value = .win at hwin
  have hQdef : (Y ∪ K).sum (fun x ↦ x) - (b + c) = K.sum (fun x ↦ x) := by omega
  rw [hQdef] at hwin
  have hZ : Z = insert b K := (Finset.insert_erase hbZ).symm
  have hrem : insert b (C \ Y) \ Z = C \ (Y ∪ K) := by
    ext x
    by_cases he : x = b
    · subst x
      simp [hZ, hb]
    · simp [hZ, he, and_assoc]
  have hZsum := Finset.sum_erase_add Z (fun x : ℕ ↦ x) hbZ
  try simp only at hZsum
  change K.sum (fun x ↦ x) + b = Z.sum (fun x ↦ x) at hZsum
  have hZdef : Z.sum (fun x ↦ x) - b = K.sum (fun x ↦ x) := by omega
  change (⟨insert b (C \ Y) \ Z, Z.sum (fun x ↦ x) - b⟩ : Position).value = .win
  rw [hrem, hZdef]
  exact hwin

/-- The reserve-containing completed repair has losing outcome for its original mover. -/
theorem repair_turn_loses
    (C Y Z : Finset ℕ) (b c final repairFinal : ℕ) (hbpos : 0 < b) (hcpos : 0 < c)
    (hb : b ∉ C) (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final)
    (hbY : b ∉ Y) (heq : Y.sum (fun x ↦ x) = b + c)
    (repair : TurnSet ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z repairFinal) (hbZ : b ∈ Z) :
    (completedTurnEndpoint ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z).toPosition.value.neg = .loss := by
  rw [repair_endpoint_win C Y Z b c final repairFinal hbpos hcpos hb hloss turn hbY heq repair hbZ]
  rfl

/-- At equality every nonlosing whole-turn witness must avoid the reserve. -/
theorem nonloss_iff_avoiding_reserve
    (C Y : Finset ℕ) (b c final : ℕ) (hbpos : 0 < b) (hcpos : 0 < c)
    (hb : b ∉ C) (hloss : (⟨C, b + c⟩ : Position).value = .loss)
    (turn : TurnSet ⟨⟨insert b C, c⟩, .p1⟩ Y final)
    (hbY : b ∉ Y) (heq : Y.sum (fun x ↦ x) = b + c) :
    (⟨insert b (C \ Y), b⟩ : Position).value ≠ .loss ↔
      ∃ Z repairFinal, TurnSet ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z repairFinal ∧
        b ∉ Z ∧
        (completedTurnEndpoint ⟨⟨insert b (C \ Y), b⟩, .p1⟩ Z).toPosition.value ≠ .win := by
  have hcatch : ¬ (insert b (C \ Y)).sum (fun x ↦ x) < b := by
    have hs := Finset.single_le_sum (f := fun x : ℕ ↦ x) (fun _ _ ↦ Nat.zero_le _)
      (show b ∈ insert b (C \ Y) by simp)
    change b ≤ (insert b (C \ Y)).sum (fun x ↦ x) at hs
    omega
  rw [Position.value_ne_loss_iff_exists_turn_set _ (by simp) hcatch]
  constructor
  · rintro ⟨Z, repairFinal, repair, hsafe⟩
    refine ⟨Z, repairFinal, repair, ?_, hsafe⟩
    intro hbZ
    exact hsafe (repair_endpoint_win C Y Z b c final repairFinal hbpos hcpos hb hloss
      turn hbY heq repair hbZ)
  · rintro ⟨Z, repairFinal, repair, _, hsafe⟩
    exact ⟨Z, repairFinal, repair, hsafe⟩

end CatchUp.EqualityReserveObstruction
