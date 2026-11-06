/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/FullGapDensityFamily.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.PairClassification
public import CatchUp.BoCowgill.ExactSumLossObstruction

/-! # An unbounded family obstructing density-free strategic gap closure -/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.FullGapDensityFamily

open Finset
open CatchUpSearch.TopFourClassification
open CatchUpSearch.TopFourClassification (value_singleton)
open CatchUpSearch.TopFourClassification (value_eq_win_iff)
open CatchUpSearch.TopFourClassification (value_eq_loss_iff)
open CatchUpSearch.TopFourClassification (pairFormulaExact)
open CatchUp (Position.move_outcome_eq_loss_of_value_eq_loss)

def support (a : ℕ) : Finset ℕ := {a, a + 1, 2 * a + 1, 2 * a + 2}
def residual (a : ℕ) : Finset ℕ := {a, a + 1, 2 * a + 1}
def block (a : ℕ) : Finset ℕ := {a, 2 * a + 1}

/-- Taking the larger counter wins when its overshoot exceeds the smaller counter. -/
theorem pair_win_of_deficit_lt_gap (u v e : ℕ) (huv : u < v) (hgap : e < v - u) :
    (⟨{u, v}, e⟩ : Position).value = .win := by
  have hcatch : ¬ ({u, v} : Finset ℕ).sum (fun x ↦ x) < e := by
    simp [ne_of_lt huv]
    omega
  apply (value_eq_win_iff ⟨{u, v}, e⟩ (by simp) hcatch).2
  refine ⟨v, by simp, ?_⟩
  have he : ¬ v < e := by omega
  have herase : ({u, v} : Finset ℕ).erase v = {u} := by
    ext x
    simp
    omega
  simp only [Position.moveOutcome, Position.afterPick, he, ite_false]
  rw [herase, value_singleton]
  simp [show ¬ v - e < u by omega, show v - e ≠ u by omega, Outcome.neg]

theorem close_pair_loss (a : ℕ) (ha : 2 ≤ a) :
    (⟨{2 * a + 1, 2 * a + 2}, a⟩ : Position).value = .loss := by
  rw [value_pair_exact (2 * a + 1) (2 * a + 2) a (by omega) (by omega) (by omega)]
  simp only [pairFormulaExact]
  split_ifs <;> first | rfl | omega

theorem low_pair_win (a : ℕ) (ha : 2 ≤ a) :
    (⟨{a, a + 1}, a + 2⟩ : Position).value = .win := by
  rw [value_pair_exact a (a + 1) (a + 2) (by omega) (by omega) (by omega)]
  simp only [pairFormulaExact]
  split_ifs <;> first | rfl | omega

private theorem erase_three_left (u v w : ℕ) (huv : u < v) (hvw : v < w) :
    ({u, v, w} : Finset ℕ).erase u = {v, w} := by
  ext x
  simp
  omega

private theorem erase_three_middle (u v w : ℕ) (huv : u < v) (hvw : v < w) :
    ({u, v, w} : Finset ℕ).erase v = {u, w} := by
  ext x
  simp
  omega

private theorem erase_three_right (u v w : ℕ) (huv : u < v) (hvw : v < w) :
    ({u, v, w} : Finset ℕ).erase w = {u, v} := by
  ext x
  simp
  omega

private theorem catchable_of_member (S : Finset ℕ) (m d : ℕ) (hm : m ∈ S) (hd : d ≤ m) :
    ¬ S.sum (fun x ↦ x) < d := by
  have hs := Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hm
  omega

theorem child_low_loss (a : ℕ) (ha : 2 ≤ a) :
    (⟨{a + 1, 2 * a + 1, 2 * a + 2}, 2 * a + 1⟩ : Position).value = .loss := by
  apply (value_eq_loss_iff _ (by simp)
    (catchable_of_member _ (2 * a + 1) _ (by simp) le_rfl)).2
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with hx | hx | hx
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show a + 1 < 2 * a + 1 by omega, ite_true,
      erase_three_left (a + 1) (2 * a + 1) (2 * a + 2) (by omega) (by omega),
      show 2 * a + 1 - (a + 1) = a by omega]
    exact close_pair_loss a ha
  · subst x
    simp only [Position.moveOutcome, Position.afterPick, Nat.lt_irrefl, ite_false,
      erase_three_middle (a + 1) (2 * a + 1) (2 * a + 2) (by omega) (by omega), Nat.sub_self]
    rw [pair_win_of_deficit_lt_gap (a + 1) (2 * a + 2) 0 (by omega) (by omega)]
    rfl
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show ¬ 2 * a + 2 < 2 * a + 1 by omega, ite_false,
      erase_three_right (a + 1) (2 * a + 1) (2 * a + 2) (by omega) (by omega),
      show 2 * a + 2 - (2 * a + 1) = 1 by omega]
    rw [pair_win_of_deficit_lt_gap (a + 1) (2 * a + 1) 1 (by omega) (by omega)]
    rfl

theorem child_second_loss (a : ℕ) (ha : 2 ≤ a) :
    (⟨{a, 2 * a + 1, 2 * a + 2}, 2 * a⟩ : Position).value = .loss := by
  apply (value_eq_loss_iff _ (by simp)
    (catchable_of_member _ (2 * a + 2) (2 * a) (by simp) (by omega))).2
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with hx | hx | hx
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show a < 2 * a by omega, ite_true,
      erase_three_left (a) (2 * a + 1) (2 * a + 2) (by omega) (by omega),
      show (2 * a) - (a) = a by omega]
    exact close_pair_loss a ha
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show ¬ (2 * a + 1) < 2 * a by omega, ite_false,
      erase_three_middle (a) (2 * a + 1) (2 * a + 2) (by omega) (by omega),
      show (2 * a + 1) - (2 * a) = 1 by omega]
    rw [pair_win_of_deficit_lt_gap a (2 * a + 2) 1 (by omega) (by omega)]
    rfl
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show ¬ (2 * a + 2) < 2 * a by omega, ite_false,
      erase_three_right (a) (2 * a + 1) (2 * a + 2) (by omega) (by omega),
      show (2 * a + 2) - (2 * a) = 2 by omega]
    rw [pair_win_of_deficit_lt_gap a (2 * a + 1) 2 (by omega) (by omega)]
    rfl

theorem child_third_loss (a : ℕ) (ha : 2 ≤ a) :
    (⟨{a, a + 1, 2 * a + 2}, a⟩ : Position).value = .loss := by
  apply (value_eq_loss_iff _ (by simp)
    (catchable_of_member _ (2 * a + 2) a (by simp) (by omega))).2
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with hx | hx | hx
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show ¬ (a) < a by omega, ite_false,
      erase_three_left (a) (a + 1) (2 * a + 2) (by omega) (by omega),
      show (a) - (a) = 0 by omega]
    rw [pair_win_of_deficit_lt_gap (a + 1) (2 * a + 2) 0 (by omega) (by omega)]
    rfl
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show ¬ (a + 1) < a by omega, ite_false,
      erase_three_middle (a) (a + 1) (2 * a + 2) (by omega) (by omega),
      show (a + 1) - (a) = 1 by omega]
    rw [pair_win_of_deficit_lt_gap a (2 * a + 2) 1 (by omega) (by omega)]
    rfl
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show ¬ (2 * a + 2) < a by omega, ite_false,
      erase_three_right (a) (a + 1) (2 * a + 2) (by omega) (by omega),
      show (2 * a + 2) - (a) = a + 2 by omega]
    rw [low_pair_win a ha]
    rfl

theorem child_top_loss (a : ℕ) (ha : 2 ≤ a) :
    (⟨{a, a + 1, 2 * a + 1}, a - 1⟩ : Position).value = .loss := by
  apply (value_eq_loss_iff _ (by simp)
    (catchable_of_member _ (2 * a + 1) (a - 1) (by simp) (by omega))).2
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with hx | hx | hx
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show ¬ (a) < a - 1 by omega, ite_false,
      erase_three_left (a) (a + 1) (2 * a + 1) (by omega) (by omega),
      show (a) - (a - 1) = 1 by omega]
    rw [pair_win_of_deficit_lt_gap (a + 1) (2 * a + 1) 1 (by omega) (by omega)]
    rfl
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show ¬ (a + 1) < a - 1 by omega, ite_false,
      erase_three_middle (a) (a + 1) (2 * a + 1) (by omega) (by omega),
      show (a + 1) - (a - 1) = 2 by omega]
    rw [pair_win_of_deficit_lt_gap a (2 * a + 1) 2 (by omega) (by omega)]
    rfl
  · subst x
    simp only [Position.moveOutcome, Position.afterPick,
      show ¬ (2 * a + 1) < a - 1 by omega, ite_false,
      erase_three_right (a) (a + 1) (2 * a + 1) (by omega) (by omega),
      show (2 * a + 1) - (a - 1) = a + 2 by omega]
    rw [low_pair_win a ha]
    rfl

theorem ancestor_loss (a : ℕ) (ha : 2 ≤ a) :
    (⟨support a, 3 * a + 1⟩ : Position).value = .loss := by
  have hmem : 2 * a + 2 ∈ support a := by simp [support]
  apply (value_eq_loss_iff _ (by simp [support]) (by
    have hs := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x)
      (show ({a, 2 * a + 2} : Finset ℕ) ⊆ support a by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [support])
    simp [show a ≠ 2 * a + 2 by omega] at hs
    change ¬ (support a).sum (fun x ↦ x) < 3 * a + 1
    omega)).2
  intro x hx
  simp only [support, mem_insert, mem_singleton] at hx
  rcases hx with hx | hx | hx | hx
  · subst x
    have herase : (support a).erase (a) = {a + 1, 2 * a + 1, 2 * a + 2} := by
      ext y
      simp [support]
      omega
    simp only [Position.moveOutcome, Position.afterPick,
      show a < 3 * a + 1 by omega, ite_true, herase,
      show 3 * a + 1 - (a) = 2 * a + 1 by omega]
    exact child_low_loss a ha
  · subst x
    have herase : (support a).erase (a + 1) = {a, 2 * a + 1, 2 * a + 2} := by
      ext y
      simp [support]
      omega
    simp only [Position.moveOutcome, Position.afterPick,
      show a + 1 < 3 * a + 1 by omega, ite_true, herase,
      show 3 * a + 1 - (a + 1) = 2 * a by omega]
    exact child_second_loss a ha
  · subst x
    have herase : (support a).erase (2 * a + 1) = {a, a + 1, 2 * a + 2} := by
      ext y
      simp [support]
      omega
    simp only [Position.moveOutcome, Position.afterPick,
      show 2 * a + 1 < 3 * a + 1 by omega, ite_true, herase,
      show 3 * a + 1 - (2 * a + 1) = a by omega]
    exact child_third_loss a ha
  · subst x
    have herase : (support a).erase (2 * a + 2) = {a, a + 1, 2 * a + 1} := by
      ext y
      simp [support]
      omega
    simp only [Position.moveOutcome, Position.afterPick,
      show 2 * a + 2 < 3 * a + 1 by omega, ite_true, herase,
      show 3 * a + 1 - (2 * a + 2) = a - 1 by omega]
    exact child_top_loss a ha

theorem residual_loss (a : ℕ) (ha : 2 ≤ a) :
    (⟨residual a, a - 1⟩ : Position).value = .loss := child_top_loss a ha

theorem successor_eq (a : ℕ) (ha : 2 ≤ a) :
    (⟨support a, 3 * a + 1⟩ : Position).afterPick (2 * a + 2) = ⟨residual a, a - 1⟩ := by
  have herase : (support a).erase (2 * a + 2) = residual a := by
    ext x
    simp [support, residual]
    omega
  simp [Position.afterPick, show 2 * a + 2 < 3 * a + 1 by omega, herase,
    show 3 * a + 1 - (2 * a + 2) = a - 1 by omega]

theorem winning_residual_opening (a : ℕ) (ha : 2 ≤ a) :
    (afterOpening (support a \ block a) (2 * a + 2)).value = .loss := by
  have he : afterOpening (support a \ block a) (2 * a + 2) = ⟨{a + 1}, 2 * a + 2⟩ := by
    change (⟨(support a \ block a).erase (2 * a + 2), 2 * a + 2⟩ : Position) = _
    congr 1
    ext x
    simp [support, block]
    omega
  rw [he, value_singleton]
  simp [show ¬ 2 * a + 2 < a + 1 by omega, show 2 * a + 2 ≠ a + 1 by omega]

private theorem powerset_singleton_calc (x : ℕ) : ({x} : Finset ℕ).powerset = {∅, {x}} := by
  change (insert x (∅ : Finset ℕ)).powerset = _
  rw [powerset_insert, powerset_empty]
  simp

theorem exact_block_unique (a : ℕ) (ha : 2 ≤ a) (B : Finset ℕ)
    (hB : B ⊆ support a) (hsum : B.sum id = 3 * a + 1) : B = block a := by
  have hm := mem_powerset.mpr hB
  simp only [support, powerset_insert, powerset_singleton_calc, image_union, image_insert,
    image_singleton, mem_union, mem_insert, mem_singleton, or_assoc] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp (disch := (try simp <;> omega)) only
    [Finset.sum_insert, Finset.sum_singleton, Finset.sum_empty, id_eq] at hsum
  all_goals first | rfl | omega

theorem gap_unrepresentable (a : ℕ) (ha : 2 ≤ a) (B : Finset ℕ)
    (hB : B ⊆ support a) : B.sum id ≠ a - 1 := by
  intro hsum
  by_cases he : B = ∅
  · simp [he] at hsum
    omega
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hmem := hB hx
    simp only [support, mem_insert, mem_singleton] at hmem
    have hax : a ≤ x := by rcases hmem with h | h | h | h <;> omega
    have hs := Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hx
    change x ≤ B.sum id at hs
    omega

theorem block_arithmetic (a : ℕ) (ha : 2 ≤ a) :
    (block a).Nonempty ∧ block a ⊆ support a ∧ (block a).sum id = 3 * a + 1 ∧
    block a ⊆ Icc 1 (2 * a + 1) ∧ 2 * a + 1 ∈ block a ∧
    2 * a + 1 < 2 * a + 2 ∧ 2 * a + 2 ∈ support a \ block a := by
  refine ⟨by simp [block], ?_, ?_, ?_, by simp [block], by omega, ?_⟩
  · intro x hx
    simp only [block, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [support]
  · simp [block, show a ≠ 2 * a + 1 by omega]
    omega
  · intro x hx
    simp only [block, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> exact mem_Icc.mpr ⟨by omega, by omega⟩
  · simp [support, block, show 2 * a + 2 ≠ a by omega]

theorem support_subset (a N : ℕ) (ha : 2 ≤ a) (hN : 3 * a + 1 ≤ N) :
    support a ⊆ Icc 1 N := by
  intro x hx
  simp only [support, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact mem_Icc.mpr ⟨by omega, by omega⟩

theorem support_card (a : ℕ) (ha : 2 ≤ a) : (support a).card = 4 := by
  simp (disch := (try simp <;> omega)) [support, Finset.card_insert_of_notMem]

theorem effective_sum (a : ℕ) (ha : 2 ≤ a) :
    (support a).sum id + (3 * a + 1) = 9 * a + 5 := by
  simp (disch := (try simp <;> omega)) [support, Finset.sum_insert]
  omega

theorem effective_even_iff_odd (a : ℕ) (ha : 2 ≤ a) :
    Even ((support a).sum id + (3 * a + 1)) ↔ Odd a := by
  rw [effective_sum a ha]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k - (4 * a + 3), ?_⟩
    omega
  · rintro ⟨k, hk⟩
    exact ⟨9 * k + 7, by omega⟩

theorem hole_count (a N : ℕ) (ha : 2 ≤ a) (hN : 3 * a + 1 ≤ N) :
    (Icc 1 N \ support a).card = N - 4 := by
  rw [card_sdiff_of_subset (support_subset a N ha hN), support_card a ha]
  simp

theorem density_fails (a N : ℕ) (ha : 3 ≤ a) (hN : 3 * a + 1 ≤ N) :
    3 * a + 1 < 2 * (Icc 1 N \ support a).card + 1 := by
  rw [hole_count a N (by omega) hN]
  omega

theorem every_residual_pick_loses (a : ℕ) (ha : 2 ≤ a) (x : ℕ) (hx : x ∈ residual a) :
    (⟨residual a, a - 1⟩ : Position).moveOutcome x = .loss := by
  exact Position.move_outcome_eq_loss_of_value_eq_loss _ hx
    (catchable_of_member _ a _ (by simp [residual]) (by change a - 1 ≤ a; omega))
    (residual_loss a ha)

theorem every_ancestor_pick_loses (a : ℕ) (ha : 2 ≤ a) (x : ℕ) (hx : x ∈ support a) :
    (⟨support a, 3 * a + 1⟩ : Position).moveOutcome x = .loss := by
  have hb := block_arithmetic a ha
  have hs := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x) hb.2.1
  change (block a).sum id ≤ (support a).sum id at hs
  rw [hb.2.2.1] at hs
  exact Position.move_outcome_eq_loss_of_value_eq_loss _ hx (by
    change ¬ (support a).sum id < 3 * a + 1
    omega) (ancestor_loss a ha)

/-- An unbounded even counterfamily to full strategic gap closure with density omitted. -/
theorem odd_family_obstruction (a : ℕ) (ha : 3 ≤ a) (hodd : Odd a) :
    support a ⊆ Icc 1 (3 * a + 1) ∧
    Even ((support a).sum id + (3 * a + 1)) ∧
    3 * a + 1 < 2 * (Icc 1 (3 * a + 1) \ support a).card + 1 ∧
    (⟨support a, 3 * a + 1⟩ : Position).value = .loss ∧
    (block a).Nonempty ∧ block a ⊆ support a ∧ (block a).sum id = 3 * a + 1 ∧
    (∀ B : Finset ℕ, B ⊆ support a → B.sum id = 3 * a + 1 → B = block a) ∧
    block a ⊆ Icc 1 (2 * a + 1) ∧ 2 * a + 1 ∈ block a ∧
    2 * a + 1 < 2 * a + 2 ∧ 2 * a + 2 ∈ support a \ block a ∧
    2 * a + 2 < 3 * a + 1 ∧ 3 * a + 1 - (2 * a + 2) = a - 1 ∧
    1 ≤ a - 1 ∧ a - 1 < (Icc 1 (3 * a + 1) \ support a).card ∧
    (∀ B : Finset ℕ, B ⊆ support a → B.sum id ≠ a - 1) ∧
    (afterOpening (support a \ block a) (2 * a + 2)).value = .loss ∧
    (⟨support a, 3 * a + 1⟩ : Position).afterPick (2 * a + 2) = ⟨residual a, a - 1⟩ ∧
    ((⟨support a, 3 * a + 1⟩ : Position).afterPick (2 * a + 2)).value = .loss := by
  have ha2 : 2 ≤ a := by omega
  rcases block_arithmetic a ha2 with ⟨hne, hsub, hsum, hbound, htop, hlt, hw⟩
  refine ⟨support_subset a _ ha2 le_rfl, (effective_even_iff_odd a ha2).mpr hodd,
    density_fails a _ ha le_rfl, ancestor_loss a ha2, hne, hsub, hsum,
    exact_block_unique a ha2, hbound, htop, hlt, hw, by omega, by omega, by omega,
    ?_, gap_unrepresentable a ha2, winning_residual_opening a ha2,
    successor_eq a ha2, ?_⟩
  · rw [hole_count a _ ha2 le_rfl]
    omega
  · rw [successor_eq a ha2]
    exact residual_loss a ha2

end CatchUp.FullGapDensityFamily
