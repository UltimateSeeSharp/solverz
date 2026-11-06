/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DeficitCrossingEntry.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.PairEntranceShadow

/-!
# A higher losing deficit forces the possible lower-deficit entries

Deleting a reserved counter from the high loss supplies the existing shadow
contract. Every singleton low turn except the reserve and the equality counter
leaves a winning opponent endpoint. This is an entry restriction, not a proof
that the lower position has a safe move.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DeficitCrossingEntry

open CatchUp (Position.move_outcome_eq_loss_of_value_eq_loss)

/-- At low deficit `l`, only `a` and the equality counter `l+a` can be safe. -/
theorem first_move_eq_loss (S : Finset ℕ) (l a x : ℕ)
    (ha : a ∈ S) (hmin : ∀ y ∈ S, l ≤ y)
    (hhigh : (⟨S, l + 2 * a⟩ : Position).value = .loss)
    (hx : x ∈ S) (hxa : x ≠ a) (hxe : x ≠ l + a) :
    (⟨S, l⟩ : Position).moveOutcome x = .loss := by
  by_cases hbelow : a < l + 2 * a
  · have hshadow := PairEntranceShadow.loss_after_subsum S {a} (l + 2 * a)
      (singleton_subset_iff.mpr ha) (by simpa using hbelow) hhigh
    have hs : (⟨S.erase a, a + l⟩ : Position).value = .loss := by
      simpa [sdiff_singleton_eq_erase, show l + 2 * a - a = a + l by omega]
        using hshadow
    have hturn : TurnSet ⟨⟨insert a (S.erase a), l⟩, .p1⟩ {x} x :=
      ⟨by simp, by simpa [insert_erase ha] using singleton_subset_iff.mpr hx,
        by simpa using hmin x hx, Or.inl rfl⟩
    have hw := PairEntranceShadow.endpoint_win_of_total_ne (S.erase a) {x} a l x
      (by simp) hs hturn (by simpa using Ne.symm hxa)
      (by simpa [Nat.add_comm] using hxe)
    have heq : insert a (S.erase a \ {x}) = S.erase x := by
      ext y
      by_cases hy : y = a <;> simp [hy, ha, Ne.symm hxa, and_comm]
    simpa [Position.moveOutcome, Position.afterPick, not_lt.mpr (hmin x hx), heq, Outcome.neg]
      using congrArg Outcome.neg hw
  · have hz : l + 2 * a = l := by omega
    apply Position.move_outcome_eq_loss_of_value_eq_loss (⟨S, l⟩ : Position) hx
    · have hl : l = 0 := by omega
      simp [hl]
    · simpa [hz] using hhigh

/-- If the equality counter is absent, lower nonloss is exactly safety of the reserved entry. -/
theorem nonloss_iff_entry (S : Finset ℕ) (l a : ℕ)
    (ha : a ∈ S) (hmin : ∀ y ∈ S, l ≤ y)
    (hhigh : (⟨S, l + 2 * a⟩ : Position).value = .loss) (he : l + a ∉ S) :
    (⟨S, l⟩ : Position).value ≠ .loss ↔
      (⟨S.erase a, a - l⟩ : Position).value ≠ .win := by
  have hcatch : ¬ S.sum (fun y ↦ y) < l := by
    exact not_lt.mpr ((hmin a ha).trans
      (Finset.single_le_sum (f := fun y : ℕ ↦ y) (fun _ _ ↦ Nat.zero_le _) ha))
  rw [Position.value_eq_best_move_outcome _ (Finset.ne_empty_of_mem ha) hcatch,
    Outcome.best_ne_loss_iff]
  constructor
  · rintro ⟨outcome, houtcome, hsafe⟩
    rcases List.mem_map.mp houtcome with ⟨⟨x, hx⟩, _, rfl⟩
    by_cases hxa : x = a
    · subst x
      simpa [Position.moveOutcome, Position.afterPick, not_lt.mpr (hmin a ha)] using hsafe
    · exact False.elim (hsafe (first_move_eq_loss S l a x ha hmin hhigh hx hxa
        (fun h ↦ he (h ▸ hx))))
  · intro hentry
    refine ⟨(⟨S, l⟩ : Position).moveOutcome a,
      List.mem_map.mpr ⟨⟨a, ha⟩, by simp, rfl⟩, ?_⟩
    simpa [Position.moveOutcome, Position.afterPick, not_lt.mpr (hmin a ha)] using hentry

/-- In the anchor-eight setting, every first counter other than three loses at deficit two. -/
theorem eight_to_two_first_move (S : Finset ℕ) (x : ℕ)
    (h3 : 3 ∈ S) (hmin : ∀ y ∈ S, 2 ≤ y) (h5 : 5 ∉ S)
    (hhigh : (⟨S, 8⟩ : Position).value = .loss) (hx : x ∈ S) (hx3 : x ≠ 3) :
    (⟨S, 2⟩ : Position).moveOutcome x = .loss := by
  exact first_move_eq_loss S 2 3 x h3 hmin hhigh hx hx3
    (fun h ↦ h5 (by simpa [h] using hx))

/-- The anchor-eight reflection reduces exactly to nonwinning after the forced first pick three. -/
theorem eight_to_two_nonloss_iff (S : Finset ℕ)
    (h3 : 3 ∈ S) (hmin : ∀ y ∈ S, 2 ≤ y) (h5 : 5 ∉ S)
    (hhigh : (⟨S, 8⟩ : Position).value = .loss) :
    (⟨S, 2⟩ : Position).value ≠ .loss ↔
      (⟨S.erase 3, 1⟩ : Position).value ≠ .win := by
  exact nonloss_iff_entry S 2 3 h3 hmin hhigh h5

end CatchUp.DeficitCrossingEntry
