/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/RootUpperEightFrontier.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.RootUpperReentry
public import CatchUp.DeficitCrossingEntry

/-!
# The actual eight-opening branch reaches a two-anchor double loss

Every legal opponent turn is retained. The remaining double-loss obstruction
is explicit; no exclusion of that obstruction, density preservation, or proof
of the interval conjecture is asserted.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.RootUpperEightFrontier

/-- Copy of `CatchUp.WinningOpening`'s private lemma; public, its name would clash with
`CatchUp.Best`'s differently stated one. -/
private theorem Outcome.best_eq_win_iff (outcomes : List Outcome) :
    Outcome.best outcomes = .win ↔ ∃ outcome ∈ outcomes, outcome = .win := by
  rw [← not_iff_not]
  simp
  constructor
  · intro hall hmem
    exact hall .win hmem rfl
  · intro hnot outcome hmem heq
    subst outcome
    exact hnot hmem

private theorem turn_set_at_three (C Y : Finset ℕ) (final : ℕ)
    (hmin : ∀ x ∈ C, 2 ≤ x)
    (turn : TurnSet ⟨⟨C, 3⟩, .p1⟩ Y final) :
    Y = {final} ∨ (Y = {2, final} ∧ final ≠ 2) := by
  rcases turn.preparation_below with hsingle | hbelow
  · exact Or.inl hsingle
  · have hprep : ∀ x ∈ Y.erase final, x = 2 := by
      intro x hx
      have hlow := hmin x (turn.chosen_subset (mem_of_mem_erase hx))
      have hsum := Finset.single_le_sum (f := fun y : ℕ ↦ y)
        (fun y _ ↦ Nat.zero_le y) hx
      change x ≤ (Y.erase final).sum (fun y ↦ y) at hsum
      change (Y.erase final).sum (fun x ↦ x) < 3 at hbelow
      omega
    by_cases h2 : 2 ∈ Y.erase final
    · right
      refine ⟨?_, Ne.symm (mem_erase.mp h2).1⟩
      have he : Y.erase final = {2} :=
        eq_singleton_iff_unique_mem.mpr ⟨h2, hprep⟩
      have hswap : ({final, 2} : Finset ℕ) = {2, final} := by
        ext x
        simp [or_comm]
      simpa only [insert_erase turn.final_mem, hswap]
        using congrArg (insert final) he
    · left
      apply eq_singleton_iff_unique_mem.mpr
      refine ⟨turn.final_mem, ?_⟩
      intro x hx
      by_contra hne
      have hp := hprep x (mem_erase.mpr ⟨hne, hx⟩)
      exact h2 (hp ▸ mem_erase.mpr ⟨hne, hx⟩)

private theorem turn_sum_ne_eight (C Y : Finset ℕ) (final : ℕ)
    (hmin : ∀ x ∈ C, 2 ≤ x) (h6 : 6 ∉ C) (h8 : 8 ∉ C)
    (turn : TurnSet ⟨⟨C, 3⟩, .p1⟩ Y final) :
    Y.sum (fun x ↦ x) ≠ 8 := by
  intro he
  rcases turn_set_at_three C Y final hmin turn with hs | ⟨hp, hn⟩
  · have hf : final = 8 := by simpa [hs] using he
    exact h8 (hf ▸ turn.chosen_subset turn.final_mem)
  · have hf : final = 6 := by
      have he' : 2 + final = 8 := by
        simpa [hp, Ne.symm hn] using he
      omega
    exact h6 (hf ▸ turn.chosen_subset turn.final_mem)

private theorem reserve_five_turn (C Y : Finset ℕ) (final : ℕ)
    (hmin : ∀ x ∈ C, 2 ≤ x)
    (turn : TurnSet ⟨⟨C, 3⟩, .p1⟩ Y final) (h5Y : 5 ∈ Y) :
    Y = {5} ∨ Y = {2, 5} := by
  rcases turn_set_at_three C Y final hmin turn with hs | ⟨hp, _⟩
  · left
    have hf : final = 5 := by simpa [hs, eq_comm] using h5Y
    simpa [hf] using hs
  · right
    have hf : final = 5 := by simpa [hp, eq_comm] using h5Y
    simpa [hf] using hp

/-- Negation turns a win into a loss and back (solverz port: v4.35's simp needs it stated). -/
private theorem outcome_neg_eq_win {o : Outcome} : o.neg = .win ↔ o = .loss := by
  cases o <;> simp [Outcome.neg]

/-- A low loss at deficit two and its losing eight-shadow force deficit-one loss
after deleting counters two and three. -/
theorem core_one_loss_of_low_two_loss (C : Finset ℕ)
    (h2 : 2 ∈ C) (h3 : 3 ∈ C) (hmin : ∀ x ∈ C, 2 ≤ x)
    (hhigh : (⟨C, 8⟩ : Position).value = .loss)
    (hlow : (⟨C, 2⟩ : Position).value = .loss) :
    (⟨C \ {2, 3}, 1⟩ : Position).value = .loss := by
  have hturn : TurnSet ⟨⟨C, 2⟩, .p1⟩ {3} 3 :=
    ⟨by simp, singleton_subset_iff.mpr h3, by norm_num, Or.inl rfl⟩
  have hw : (⟨C.erase 3, 1⟩ : Position).value = .win := by
    simpa [completedTurnEndpoint, sdiff_singleton_eq_erase] using
      PairEntranceShadow.turn_endpoint_win_of_loss ⟨C, 2⟩ {3} 3 hturn hlow
  have hh : (⟨C.erase 3, 5⟩ : Position).value = .loss := by
    simpa [sdiff_singleton_eq_erase] using PairEntranceShadow.loss_after_subsum C {3} 8
      (singleton_subset_iff.mpr h3) (by norm_num) hhigh
  have h2D : 2 ∈ C.erase 3 := by simp [h2]
  have hcatch : ¬ (C.erase 3).sum (fun x ↦ x) < 1 := by
    have hs := Finset.single_le_sum (f := fun x : ℕ ↦ x)
      (fun _ _ ↦ Nat.zero_le _) h2D
    change 2 ≤ (C.erase 3).sum (fun x ↦ x) at hs
    omega
  rw [Position.value_eq_best_move_outcome _ (Finset.ne_empty_of_mem h2D) hcatch,
    Outcome.best_eq_win_iff] at hw
  obtain ⟨outcome, hmem, heq⟩ := hw
  rcases List.mem_map.mp hmem with ⟨⟨x, hx⟩, _, rfl⟩
  by_cases hx2 : x = 2
  · subst x
    have hcore : (C.erase 3).erase 2 = C \ {2, 3} := by
      ext y
      simp [and_comm, and_left_comm]
    simpa [Position.moveOutcome, Position.afterPick, hcore, outcome_neg_eq_win] using heq
  · have hbad := DeficitCrossingEntry.first_move_eq_loss (C.erase 3) 1 2 x h2D
      (fun y hy ↦ by have hp := hmin y (mem_of_mem_erase hy); omega) hh hx hx2
      (by simpa using (mem_erase.mp hx).1)
    simp only [hbad] at heq
    cases heq

/-- Either reserve-taking loss exposes the same two-anchor double loss. -/
theorem core_double_loss_of_low_loss (C : Finset ℕ)
    (h2 : 2 ∈ C) (h3 : 3 ∈ C) (hmin : ∀ x ∈ C, 2 ≤ x)
    (hhigh : (⟨C, 8⟩ : Position).value = .loss)
    (hlow : (⟨C, 2⟩ : Position).value = .loss ∨
      (⟨C.erase 2, 4⟩ : Position).value = .loss) :
    (⟨C \ {2, 3}, 1⟩ : Position).value = .loss ∧
      (⟨C \ {2, 3}, 3⟩ : Position).value = .loss := by
  constructor
  · rcases hlow with hlow | hlow
    · exact core_one_loss_of_low_two_loss C h2 h3 hmin hhigh hlow
    · have hp := PairEntranceShadow.loss_after_subsum (C.erase 2) {3} 4
        (singleton_subset_iff.mpr (by simp [h3])) (by norm_num) hlow
      have he : C.erase 2 \ {3} = C \ {2, 3} := by
        ext x
        simp [and_assoc, and_comm]
      simpa only [he, sum_singleton, show 4 - 3 = 1 by omega] using hp
  · simpa using PairEntranceShadow.loss_after_subsum C {2, 3} 8
      (by simpa only [insert_subset_iff, singleton_subset_iff] using And.intro h2 h3)
      (by norm_num) hhigh

/-- A winning reserve-five endpoint must use one of the two reserve-taking losses. -/
theorem low_loss_of_reserve_win (C : Finset ℕ)
    (hmin : ∀ x ∈ C, 2 ≤ x) (h5 : 5 ∉ C) (h6 : 6 ∉ C) (h8 : 8 ∉ C)
    (hhigh : (⟨C, 8⟩ : Position).value = .loss)
    (hwin : (⟨insert 5 C, 3⟩ : Position).value = .win) :
    (⟨C, 2⟩ : Position).value = .loss ∨
      (⟨C.erase 2, 4⟩ : Position).value = .loss := by
  by_contra hlow
  have hcatch : ¬ (insert 5 C).sum (fun x ↦ x) < 3 := by
    have hs := Finset.single_le_sum (f := fun x : ℕ ↦ x)
      (fun _ _ ↦ Nat.zero_le _) (show 5 ∈ insert 5 C by simp)
    change 5 ≤ (insert 5 C).sum (fun x ↦ x) at hs
    omega
  have hnonwin : (⟨insert 5 C, 3⟩ : Position).value ≠ .win := by
    apply (Position.value_ne_win_iff_forall_turn_sets ⟨insert 5 C, 3⟩
      (by simp) hcatch).mpr
    intro Y final turn
    have hminInsert : ∀ x ∈ insert 5 C, 2 ≤ x := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · omega
      · exact hmin x hx
    by_cases hbY : 5 ∈ Y
    · rcases reserve_five_turn (insert 5 C) Y final hminInsert turn hbY with rfl | rfl
      · simpa [completedTurnEndpoint, sdiff_singleton_eq_erase, h5] using
          (show (⟨C, 2⟩ : Position).value ≠ .loss from fun h ↦ hlow (Or.inl h))
      · have he : insert 5 C \ {2, 5} = C.erase 2 := by
          ext x
          by_cases hx : x = 5 <;> simp [hx, h5, and_comm]
        simpa [completedTurnEndpoint, he] using
          (show (⟨C.erase 2, 4⟩ : Position).value ≠ .loss from fun h ↦ hlow (Or.inr h))
    · have hne : Y.sum (fun x ↦ x) ≠ 5 + 3 := by
        simpa using turn_sum_ne_eight (insert 5 C) Y final hminInsert
          (by simp [h6]) (by simp [h8]) turn
      have hw := PairEntranceShadow.endpoint_win_of_total_ne C Y 5 3 final
        h5 hhigh turn hbY hne
      rw [PairEntranceShadow.reserve_endpoint_eq C Y 5 3 hbY, hw]
      decide
  exact hnonwin hwin

/-- A full parent loss and its genuine eight-shadow expose the double loss. -/
theorem core_double_loss_of_parent_loss (C : Finset ℕ)
    (h2 : 2 ∈ C) (h3 : 3 ∈ C) (hmin : ∀ x ∈ C, 2 ≤ x)
    (h5 : 5 ∉ C) (h6 : 6 ∉ C) (h8 : 8 ∉ C)
    (hparent : (⟨insert 5 (insert 8 C), 5⟩ : Position).value = .loss)
    (hhigh : (⟨C, 8⟩ : Position).value = .loss) :
    (⟨C \ {2, 3}, 1⟩ : Position).value = .loss ∧
      (⟨C \ {2, 3}, 3⟩ : Position).value = .loss := by
  have turn : TurnSet ⟨⟨insert 5 (insert 8 C), 5⟩, .p1⟩ {8} 8 :=
    ⟨by simp, by simp, by norm_num, Or.inl rfl⟩
  have hw := PairEntranceShadow.turn_endpoint_win_of_loss
    ⟨insert 5 (insert 8 C), 5⟩ {8} 8 turn hparent
  have hwin : (⟨insert 5 C, 3⟩ : Position).value = .win := by
    simpa [completedTurnEndpoint, sdiff_singleton_eq_erase, erase_insert_of_ne, h8] using hw
  exact core_double_loss_of_low_loss C h2 h3 hmin hhigh
    (low_loss_of_reserve_win C hmin h5 h6 h8 hhigh hwin)

/-- The actual interval eight-shadow forces double loss on `{4,7} ∪ [9,N]`. -/
theorem interval_eight_shadow_forces_double_loss (N : ℕ) (hN : 11 ≤ N)
    (hparent : (⟨Icc 2 N \ {6}, 5⟩ : Position).value = .loss)
    (hhigh : (⟨Icc 2 N \ {5, 6, 8}, 8⟩ : Position).value = .loss) :
    (⟨{4, 7} ∪ Icc 9 N, 1⟩ : Position).value = .loss ∧
      (⟨{4, 7} ∪ Icc 9 N, 3⟩ : Position).value = .loss := by
  let C := Icc 2 N \ {5, 6, 8}
  have h2 : 2 ∈ C := by simp [C]; omega
  have h3 : 3 ∈ C := by simp [C]; omega
  have hmin : ∀ x ∈ C, 2 ≤ x := by
    intro x hx
    exact (mem_Icc.mp (mem_sdiff.mp hx).1).1
  have h5 : 5 ∉ C := by simp [C]
  have h6 : 6 ∉ C := by simp [C]
  have h8 : 8 ∉ C := by simp [C]
  have hparentSet : insert 5 (insert 8 C) = Icc 2 N \ {6} := by
    ext x
    simp only [C, mem_insert, mem_sdiff, mem_Icc, mem_singleton]
    omega
  have hp : (⟨insert 5 (insert 8 C), 5⟩ : Position).value = .loss := by
    simpa only [hparentSet] using hparent
  have he : C \ {2, 3} = {4, 7} ∪ Icc 9 N := by
    ext x
    simp only [C, mem_union, mem_insert, mem_sdiff, mem_Icc, mem_singleton]
    omega
  simpa only [he] using core_double_loss_of_parent_loss C h2 h3 hmin h5 h6 h8 hp hhigh

/-- A losing original lower-ray parent either reenters at a genuine opening at
least nine, or retains the eight-shadow and the explicit two-anchor double loss. -/
theorem interval_parent_loss_frontier (N : ℕ) (hN : 11 ≤ N)
    (hparent : (⟨Icc 2 N \ {6}, 5⟩ : Position).value = .loss) :
    (∃ w ∈ Icc 2 N \ {5, 6}, 9 ≤ w ∧
      (afterOpening (Icc 2 N \ {5, 6}) w).value = .loss) ∨
    ((⟨{2, 3, 4, 7} ∪ Icc 9 N, 8⟩ : Position).value = .loss ∧
      (⟨{4, 7} ∪ Icc 9 N, 1⟩ : Position).value = .loss ∧
      (⟨{4, 7} ∪ Icc 9 N, 3⟩ : Position).value = .loss) := by
  obtain ⟨w, hw, hge, hwin⟩ :=
    RootUpperReentry.interval_upper_opening_ge_eight N (by omega) hparent
  by_cases hw8 : w = 8
  · right
    subst w
    have hchild : (Icc 2 N \ {5, 6}).erase 8 = Icc 2 N \ {5, 6, 8} := by
      ext x
      simp only [mem_erase, mem_sdiff, mem_Icc, mem_insert, mem_singleton]
      tauto
    have hhigh : (⟨Icc 2 N \ {5, 6, 8}, 8⟩ : Position).value = .loss := by
      simpa only [afterOpening, hchild] using hwin
    have hC : Icc 2 N \ {5, 6, 8} = {2, 3, 4, 7} ∪ Icc 9 N := by
      ext x
      simp only [mem_union, mem_insert, mem_sdiff, mem_Icc, mem_singleton]
      omega
    exact ⟨by simpa only [hC] using hhigh,
      interval_eight_shadow_forces_double_loss N hN hparent hhigh⟩
  · exact Or.inl ⟨w, hw, by omega, hwin⟩

end CatchUp.RootUpperEightFrontier
