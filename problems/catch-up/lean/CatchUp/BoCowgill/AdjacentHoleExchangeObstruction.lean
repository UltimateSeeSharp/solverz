/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/AdjacentHoleExchangeObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Classifier

/-!
# A first-move obstruction to adjacent-hole strategy copying

At the admissible instance `N = 11, b = 4, y = 8`, the left deficit-one
position draws and the right position wins. Nevertheless, the natural counter
bijection sends every nonlosing right move to a losing left move.

This refutes direct move-by-move strategy transport, not the proposed
forbidden-jump lemma. Finite values are derived from the proved one-sided
classifier using kernel reduction, without native computation.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.AdjacentHoleExchange

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

/-- The left position at the admissible instance `N = 11, b = 4, y = 8`. -/
def exchangeLeft : Position := ⟨{2, 5, 6, 9, 10, 11}, 1⟩

/-- The right position at the same admissible instance. -/
def exchangeRight : Position := ⟨{2, 5, 6, 7, 10, 11}, 1⟩

/-- The left position draws. -/
theorem left_value : exchangeLeft.value = .draw := by
  rw [← checked_value_eq]
  decide +kernel

/-- The right position wins. -/
theorem right_value : exchangeRight.value = .win := by
  rw [← checked_value_eq]
  decide +kernel
private theorem checked_left_moves :
    ∀ x : {x // x ∈ exchangeLeft.remaining},
      checkedValue (exchangeLeft.afterPick x) = if x.val = 2 then .draw else .win := by
  decide +kernel

/-- Two is the only nonlosing left move; every other left move loses. -/
theorem left_move_profile (x : ℕ) (hx : x ∈ exchangeLeft.remaining) :
    exchangeLeft.moveOutcome x = if x = 2 then .draw else .loss := by
  have hlt : ¬ x < exchangeLeft.deficit := by
    simp only [exchangeLeft, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    omega
  rw [Position.moveOutcome, ite_eq_right hlt, ← checked_value_eq, checked_left_moves ⟨x, hx⟩]
  split_ifs <;> rfl
private theorem move_outcome_checked (p : Position) (x : ℕ) (h : ¬ x < p.deficit) :
    p.moveOutcome x = (checkedValue (p.afterPick x)).neg := by
  simp [Position.moveOutcome, h, checked_value_eq]
private theorem checked_right_moves :
    ∀ x : {x // x ∈ exchangeRight.remaining},
      checkedValue (exchangeRight.afterPick x) =
        if x.val = 5 then .loss else if x.val = 10 then .draw else .win := by
  decide +kernel

/-- Five wins on the right, ten draws, and every other right move loses. -/
theorem right_move_profile (x : ℕ) (hx : x ∈ exchangeRight.remaining) :
    exchangeRight.moveOutcome x =
      if x = 5 then .win else if x = 10 then .draw else .loss := by
  have hlt : ¬ x < exchangeRight.deficit := by
    simp only [exchangeRight, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    omega
  rw [move_outcome_checked _ _ hlt, checked_right_moves ⟨x, hx⟩]
  split_ifs <;> rfl

/-- The natural bijection fixes common counters and replaces seven by nine. -/
def rightToLeftCounter (x : ℕ) : ℕ := if x = 7 then 9 else x

/-- Every nonlosing right move becomes a losing left move under the natural bijection. -/
theorem safe_right_move_copies_to_loss (x : ℕ) (hx : x ∈ exchangeRight.remaining)
    (hsafe : exchangeRight.moveOutcome x ≠ .loss) :
    exchangeLeft.moveOutcome (rightToLeftCounter x) = .loss := by
  have hcases : x = 5 ∨ x = 10 := by
    rw [right_move_profile x hx] at hsafe
    split_ifs at hsafe <;> simp_all
  rcases hcases with rfl | rfl
  all_goals rw [left_move_profile _ (by decide +kernel)]
  all_goals rfl

/-- Identify the left witness with the requested punctured-interval formula. -/
theorem left_eq_requested :
    exchangeLeft = ⟨((Finset.Icc 1 11 \ {1, 3, 4}).erase 7).erase 8, 1⟩ := by
  decide +kernel

/-- Identify the right witness with the requested punctured-interval formula. -/
theorem right_eq_requested :
    exchangeRight = ⟨((Finset.Icc 1 11 \ {1, 3, 4}).erase 8).erase 9, 1⟩ := by
  decide +kernel

/-- The witness satisfies the size, parity, parameter, and three-neighbor hypotheses. -/
theorem witness_admissible :
    11 ≥ (11 : ℕ) ∧ Even (11 * (11 + 1) / 2 : ℕ) ∧
      3 ≤ (4 : ℕ) ∧ (4 : ℕ) ≤ 11 ∧
      ({7, 8, 9} : Finset ℕ) ⊆ Finset.Icc 1 11 \ {1, 3, 4} := by
  decide +kernel

/-- The natural counter correspondence maps legal right moves to legal left moves. -/
theorem right_to_left_counter_legal :
    ∀ x : {x // x ∈ exchangeRight.remaining},
      rightToLeftCounter x ∈ exchangeLeft.remaining := by
  decide +kernel

/-- Preserving a right win and a left nonloss forces two different common first moves. -/
theorem forced_first_repair (u v : ℕ)
    (hu : u ∈ exchangeLeft.remaining) (hv : v ∈ exchangeRight.remaining)
    (hleft : exchangeLeft.moveOutcome u ≠ .loss)
    (hright : exchangeRight.moveOutcome v = .win) :
    u = 2 ∧ v = 5 := by
  rw [left_move_profile u hu] at hleft
  rw [right_move_profile v hv] at hright
  split_ifs at hleft hright <;> simp_all
/-- A successful one-pick repair has deficit difference three and four unmatched counters. -/
theorem forced_first_repair_endpoints (u v : ℕ)
    (hu : u ∈ exchangeLeft.remaining) (hv : v ∈ exchangeRight.remaining)
    (hleft : exchangeLeft.moveOutcome u ≠ .loss)
    (hright : exchangeRight.moveOutcome v = .win) :
    (⟨exchangeLeft, .p1⟩ : GamePosition).afterPick u =
      ⟨⟨{5, 6, 9, 10, 11}, 1⟩, .p2⟩ ∧
    (⟨exchangeRight, .p1⟩ : GamePosition).afterPick v =
      ⟨⟨{2, 6, 7, 10, 11}, 4⟩, .p2⟩ ∧
    (((exchangeLeft.afterPick u).remaining \ (exchangeRight.afterPick v).remaining) ∪
      ((exchangeRight.afterPick v).remaining \ (exchangeLeft.afterPick u).remaining)).card = 4 := by
  rcases forced_first_repair u v hu hv hleft hright with ⟨rfl, rfl⟩
  decide +kernel

/-- An alternating-parity sparse state showing that parity order alone does not suffice. -/
def alternatingLeft : Position := ⟨{6, 11, 14, 15, 18, 23}, 1⟩

/-- Lowering six to four preserves alternating parity but reverses the value. -/
def alternatingRight : Position := ⟨{4, 11, 14, 15, 18, 23}, 1⟩

/-- The parity-only extension has a genuine forbidden jump. -/
theorem alternating_parity_jump :
    alternatingLeft.value = .loss ∧ alternatingRight.value = .win := by
  rw [← checked_value_eq alternatingLeft, ← checked_value_eq alternatingRight]
  decide +kernel

/-- Both witnesses are strictly increasing even/odd lists with even effective total. -/
theorem alternating_witness_structure :
    ([6, 11, 14, 15, 18, 23] : List ℕ).Pairwise (· < ·) ∧
    ([4, 11, 14, 15, 18, 23] : List ℕ).Pairwise (· < ·) ∧
    ([6, 11, 14, 15, 18, 23] : List ℕ).map (· % 2) = [0, 1, 0, 1, 0, 1] ∧
    ([4, 11, 14, 15, 18, 23] : List ℕ).map (· % 2) = [0, 1, 0, 1, 0, 1] ∧
    Even (alternatingLeft.deficit + alternatingLeft.remaining.sum id) ∧
    Even (alternatingRight.deficit + alternatingRight.remaining.sum id) := by
  decide +kernel

/-- The tied sparse residual behind the parity-only counterexample. -/
def parityRoot : Finset ℕ := {4, 5, 6, 11, 14, 15, 18, 23}

/-- Opening five draws despite the neighboring loss-to-win jump. -/
theorem parity_root_opening_five_draw :
    (afterOpening parityRoot 5).value = .draw := by
  rw [← checked_value_eq]
  decide +kernel

/-- Seven disjoint adjacent pairs omitted from the longer interval. -/
def omittedPairStarts : Finset ℕ :=
  {2, 7, 9, 12, 16, 19, 21}

/-- The sparse root is obtained by deleting seven adjacent pairs. -/
theorem parity_root_pair_erasure :
    parityRoot = Finset.Icc 2 23 \
      omittedPairStarts.biUnion (fun a => {a, a + 1}) := by
  decide +kernel

/-- The seven pairs are disjoint, lie in the interval, and the upper endpoint's triangular number is even. -/
theorem omitted_pairs_geometry :
    omittedPairStarts.card = 7 ∧ Even (23 * (23 + 1) / 2 : ℕ) ∧
    (∀ a : {a // a ∈ omittedPairStarts}, 2 ≤ a.val ∧ a.val + 1 ≤ 23) ∧
    (∀ a b : {a // a ∈ omittedPairStarts},
      a ≠ b → a.val + 1 < b.val ∨ b.val + 1 < a.val) := by
  decide +kernel

/-- The two sparse witnesses are the exact neighboring states at opening five. -/
theorem parity_root_neighbor_states :
    ({4, 5, 6} : Finset ℕ) ⊆ parityRoot ∧
    alternatingLeft = ⟨(parityRoot.erase 4).erase 5, 1⟩ ∧
    alternatingRight = ⟨(parityRoot.erase 5).erase 6, 1⟩ := by
  decide +kernel
/-- A non-neighbor reply saves the draw after opening five. -/
theorem parity_root_reply_eleven_draw :
    (afterOpening parityRoot 5).moveOutcome 11 = .draw := by
  rw [move_outcome_checked _ _ (by decide +kernel)]
  decide +kernel

end CatchUp.AdjacentHoleExchange
