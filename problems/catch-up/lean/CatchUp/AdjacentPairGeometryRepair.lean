/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/AdjacentPairGeometryRepair.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates.
-/
module

public import Mathlib
public import CatchUp.PairClassification
public import CatchUp.DrawOpening
public import CatchUp.ZeroDeficit

/-!
# Geometric adjacent-pair repairs

For an orphan `a` beside `{b,b+1}`, the plus-one deficit always draws.
The minus-one deficit draws exactly when `b ≥ 2*a-1`; below that threshold
it wins. The proofs track each legal pick and use only two-counter endgames.

Consequently two adjacent pairs form a drawn tied root. Three adjacent pairs
with minimum at least three are nonwinning, and they draw when the second
pair starts at least `2*a-1`. This does not prove an arbitrary-pair-count
invariant or the unbounded first-pair endpoint.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.AdjacentPairRepair

private theorem ne_loss_of_move (p : Position) (x : ℕ)
    (hx : x ∈ p.remaining) (hc : ¬ p.remaining.sum id < p.deficit)
    (hm : p.moveOutcome x ≠ .loss) : p.value ≠ .loss := by
  rw [Position.value_eq_best_move_outcome p
    (Finset.nonempty_iff_ne_empty.mp ⟨x,hx⟩) hc]
  exact (Outcome.best_ne_loss_iff _).mpr
    ⟨p.moveOutcome x,List.mem_map.mpr ⟨⟨x,hx⟩,by simp,rfl⟩,hm⟩

private theorem ne_win_of_all_moves (p : Position) (hn : p.remaining.Nonempty)
    (hc : ¬ p.remaining.sum id < p.deficit)
    (hm : ∀ x ∈ p.remaining, p.moveOutcome x ≠ .win) : p.value ≠ .win := by
  rw [Position.value_eq_best_move_outcome p (Finset.nonempty_iff_ne_empty.mp hn) hc]
  apply (Outcome.best_ne_win_iff _).mpr
  intro o ho
  obtain ⟨⟨x,hx⟩,_,rfl⟩ := List.mem_map.mp ho
  exact hm x hx

theorem adjacent_pair_draw (b : ℕ) (hb : 1 ≤ b) :
    Position.value ⟨{b,b+1},1⟩ = .draw := by
  rw [CatchUpSearch.TopFourClassification.value_pair_exact b (b+1) 1
    (by omega) (by omega) (by omega)]
  change (if 1 < b+1-b then Outcome.win else if 1 = b+1-b then Outcome.draw
    else if 1 ≤ b then Outcome.loss else if 1 < b+(b+1) then Outcome.win
    else if 1 = b+(b+1) then Outcome.draw else Outcome.loss) = .draw
  simp

private theorem empty_value (d : ℕ) :
    Position.value ⟨∅,d⟩ = if d=0 then .draw else .loss := by
  rw [Position.value.eq_def]
  simp

theorem singleton_ge_nonwin (a d : ℕ) (had : a ≤ d) :
    Position.value ⟨{a},d⟩ ≠ .win := by
  by_cases he : a = d
  · subst d
    apply ne_win_of_all_moves _ (by simp) (by simp)
    intro x hx
    have hx' : x=a := by simpa using hx
    subst x
    simp [Position.moveOutcome, Position.afterPick, empty_value, Outcome.neg]
  · have hlt : a < d := by omega
    rw [Position.value.eq_def]
    simp [hlt]

theorem pair_low_deficit_nonloss (a b d : ℕ) (hab : a < b)
    (hd : d ≤ b-a) :
    Position.value ⟨{a,b},d⟩ ≠ .loss := by
  have hmem : b ∈ ({a,b} : Finset ℕ) := by simp
  have hsum : b ≤ ({a,b} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hmem
  apply ne_loss_of_move _ b hmem (by change ¬ ({a,b} : Finset ℕ).sum id < d; omega)
  have he : ({a,b} : Finset ℕ).erase b = {a} := by ext x; simp; omega
  simp only [Position.moveOutcome, Position.afterPick,
    show ¬b < d by omega, ite_false, he, Outcome.neg_ne_loss_iff]
  exact singleton_ge_nonwin a (b-d) (by omega)

private theorem singleton_small_nonloss (b d : ℕ) (hd : d < b) :
    Position.value ⟨{b},d⟩ ≠ .loss := by
  apply ne_loss_of_move _ b (by simp) (by simpa using Nat.not_lt.mpr hd.le)
  simp [Position.moveOutcome, Position.afterPick, Nat.not_lt.mpr hd.le,
    empty_value, show b-d ≠ 0 by omega, Outcome.neg]

private theorem pair_middle_deficit_nonloss (a b d : ℕ) (ha : 0 < a)
    (hab : a < b) (had : a < d) (hdb : d ≤ b) :
    Position.value ⟨{a,b},d⟩ ≠ .loss := by
  have hmem : b ∈ ({a,b} : Finset ℕ) := by simp
  have hsum : b ≤ ({a,b} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hmem
  apply ne_loss_of_move _ a (by simp)
    (by change ¬ ({a,b} : Finset ℕ).sum id < d; omega)
  have he : ({a,b} : Finset ℕ).erase a = {b} := by ext x; simp; omega
  simp only [Position.moveOutcome, Position.afterPick, had, ite_true, he]
  exact singleton_small_nonloss b (d-a) (by omega)

/-- An orphan counter and a higher adjacent pair draw at the orphan-plus-one deficit. -/
theorem orphan_plus_draw (a b : ℕ) (ha : 2 ≤ a) (hab : a+2 ≤ b) :
    Position.value ⟨{a,b,b+1},a+1⟩ = .draw := by
  have hea : ({a,b,b+1} : Finset ℕ).erase a = {b,b+1} := by ext x; simp; omega
  have heb : ({a,b,b+1} : Finset ℕ).erase b = {a,b+1} := by ext x; simp; omega
  have hec : ({a,b,b+1} : Finset ℕ).erase (b+1) = {a,b} := by ext x; simp; omega
  have hsum : b ≤ ({a,b,b+1} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
  have hc : ¬ ({a,b,b+1} : Finset ℕ).sum id < a+1 := by omega
  have hma : (⟨{a,b,b+1},a+1⟩ : Position).moveOutcome a = .draw := by
    simp [Position.moveOutcome, Position.afterPick, hea,
      adjacent_pair_draw b (by omega)]
  apply (Outcome.eq_draw_iff _).mpr
  constructor
  · exact ne_loss_of_move _ a (by simp) hc (by rw [hma]; decide)
  · apply ne_win_of_all_moves _ ⟨a,by simp⟩ hc
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> subst x
    · rw [hma]; decide
    · simp only [Position.moveOutcome, Position.afterPick, show ¬b<a+1 by omega,
        ite_false, heb, Outcome.neg_ne_win_iff]
      exact pair_low_deficit_nonloss a (b+1) (b-(a+1)) (by omega) (by omega)
    · simp only [Position.moveOutcome, Position.afterPick, show ¬b+1<a+1 by omega,
        ite_false, hec, Outcome.neg_ne_win_iff]
      exact pair_low_deficit_nonloss a b (b+1-(a+1)) (by omega) (by omega)

/-- Separation by twice the orphan is sufficient at the orphan-minus-one deficit. -/
theorem orphan_minus_draw (a b : ℕ) (ha : 2 ≤ a) (hab : a+2 ≤ b)
    (hsep : 2*a-1 ≤ b) :
    Position.value ⟨{a,b,b+1},a-1⟩ = .draw := by
  have hea : ({a,b,b+1} : Finset ℕ).erase a = {b,b+1} := by ext x; simp; omega
  have heb : ({a,b,b+1} : Finset ℕ).erase b = {a,b+1} := by ext x; simp; omega
  have hec : ({a,b,b+1} : Finset ℕ).erase (b+1) = {a,b} := by ext x; simp; omega
  have hsum : b ≤ ({a,b,b+1} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
  have hc : ¬ ({a,b,b+1} : Finset ℕ).sum id < a-1 := by omega
  have hma : (⟨{a,b,b+1},a-1⟩ : Position).moveOutcome a = .draw := by
    simp [Position.moveOutcome, Position.afterPick, hea,
      show ¬a<a-1 by omega, show a-(a-1)=1 by omega,
      adjacent_pair_draw b (by omega), Outcome.neg]
  apply (Outcome.eq_draw_iff _).mpr
  constructor
  · exact ne_loss_of_move _ a (by simp) hc (by rw [hma]; decide)
  · apply ne_win_of_all_moves _ ⟨a,by simp⟩ hc
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> subst x
    · rw [hma]; decide
    · simp only [Position.moveOutcome, Position.afterPick, show ¬b<a-1 by omega,
        ite_false, heb, Outcome.neg_ne_win_iff]
      exact pair_low_deficit_nonloss a (b+1) (b-(a-1)) (by omega) (by omega)
    · simp only [Position.moveOutcome, Position.afterPick, show ¬b+1<a-1 by omega,
        ite_false, hec, Outcome.neg_ne_win_iff]
      exact pair_middle_deficit_nonloss a b (b+1-(a-1))
        (by omega) (by omega) (by omega) (by omega)

/-- Two disjoint actual adjacent pairs form a drawn tied game. -/
theorem two_pairs_tied_draw (a b : ℕ) (ha : 2 ≤ a) (hab : a+2 ≤ b) :
    value {a,a+1,b,b+1} = .draw := by
  apply (value_eq_draw_iff_exists_draw_after_opening _ ⟨a,by simp⟩).mpr
  refine ⟨a+1,by simp,?_⟩
  have he : ({a,a+1,b,b+1} : Finset ℕ).erase (a+1) = {a,b,b+1} := by
    ext x
    simp
    omega
  simpa only [afterOpening,he] using orphan_plus_draw a b ha hab


private theorem nonloss_of_catch (S : Finset ℕ) (d x : ℕ)
    (hx : x ∈ S) (hdx : d ≤ x)
    (hchild : Position.value ⟨S.erase x,x-d⟩ ≠ .win) :
    Position.value ⟨S,d⟩ ≠ .loss := by
  have hsum : x ≤ S.sum id := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  apply ne_loss_of_move _ x hx (by change ¬ S.sum id < d; omega)
  simpa only [Position.moveOutcome, Position.afterPick, not_lt_of_ge hdx,
    ite_false, Outcome.neg_ne_loss_iff] using hchild

private theorem nonwin_of_all_catching_children_nonloss (S : Finset ℕ) (d : ℕ)
    (hn : S.Nonempty) (hcatch : ∀ x ∈ S, d ≤ x)
    (hchild : ∀ x ∈ S, Position.value ⟨S.erase x,x-d⟩ ≠ .loss) :
    Position.value ⟨S,d⟩ ≠ .win := by
  obtain ⟨a,ha⟩ := hn
  have hsum : a ≤ S.sum id := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) ha
  have hda := hcatch a ha
  apply ne_win_of_all_moves _ ⟨a,ha⟩ (by change ¬ S.sum id < d; omega)
  intro x hx
  simpa only [Position.moveOutcome, Position.afterPick,
    not_lt_of_ge (hcatch x hx), ite_false, Outcome.neg_ne_win_iff] using hchild x hx

private theorem adjacent_pair_three_loss (a : ℕ) (ha : 3 ≤ a) :
    Position.value ⟨{a,a+1},3⟩ = .loss := by
  rw [CatchUpSearch.TopFourClassification.value_pair_exact a (a+1) 3
    (by omega) (by omega) (by omega)]
  change (if 3 < a+1-a then Outcome.win else if 3 = a+1-a then Outcome.draw
    else if 3 ≤ a then Outcome.loss else if 3 < a+(a+1) then Outcome.win
    else if 3 = a+(a+1) then Outcome.draw else Outcome.loss) = .loss
  simp [ha]

/-- At deficit two, two higher adjacent pairs are nonwinning. -/
theorem two_pairs_deficit_two_nonwin (a b : ℕ) (ha : 3 ≤ a) (hab : a+2 ≤ b) :
    Position.value ⟨{a,a+1,b,b+1},2⟩ ≠ .win := by
  apply nonwin_of_all_catching_children_nonloss _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase (a) = {a+1,b,b+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
    have hf : ({a+1,b,b+1} : Finset ℕ).erase (a+1) = {b,b+1} := by
      ext t
      simp
      omega
    rw [hf, show (a+1)-((a)-2)=3 by omega, adjacent_pair_three_loss b (by omega)]
    decide
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase (a+1) = {a,b,b+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (a) (by simp) (by omega)
    have hf : ({a,b,b+1} : Finset ℕ).erase (a) = {b,b+1} := by
      ext t
      simp
      omega
    rw [hf, show (a)-((a+1)-2)=1 by omega, adjacent_pair_draw b (by omega)]
    decide
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase (b) = {a,a+1,b+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({a,a+1,b+1} : Finset ℕ).erase (b+1) = {a,a+1} := by
      ext t
      simp
      omega
    rw [hf, show (b+1)-((b)-2)=3 by omega, adjacent_pair_three_loss a ha]
    decide
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase (b+1) = {a,a+1,b} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (b) (by simp) (by omega)
    have hf : ({a,a+1,b} : Finset ℕ).erase (b) = {a,a+1} := by
      ext t
      simp
      omega
    rw [hf, show (b)-((b+1)-2)=1 by omega, adjacent_pair_draw a (by omega)]
    decide


/-- Three adjacent pairs are nonlosing when the first pair is sufficiently separated. -/
theorem three_pairs_nonloss_of_separation (a b c : ℕ)
    (ha : 2 ≤ a) (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hsep : 2*a-1 ≤ b) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},1⟩ ≠ .loss := by
  apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
  have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (a+1) =
      {a,b,b+1,c,c+1} := by
    ext t
    simp
    omega
  rw [he, show a+1-1=a by omega]
  apply nonwin_of_all_catching_children_nonloss _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase a = {b,b+1,c,c+1} := by
      ext t
      simp
      omega
    rw [he, Nat.sub_self, position_value_zero_deficit_eq_value,
      two_pairs_tied_draw b c (by omega) hbc]
    decide
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase (b) = {a,b+1,c,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({a,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,c,c+1} := by
      ext t
      simp
      omega
    rw [hf, show (b+1)-((b)-a)=a+1 by omega, orphan_plus_draw a c ha (by omega)]
    decide
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,b,c,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (b) (by simp) (by omega)
    have hf : ({a,b,c,c+1} : Finset ℕ).erase (b) = {a,c,c+1} := by
      ext t
      simp
      omega
    rw [hf, show (b)-((b+1)-a)=a-1 by omega, orphan_minus_draw a c ha (by omega) (by omega)]
    decide
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase (c) = {a,b,b+1,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    have hf : ({a,b,b+1,c+1} : Finset ℕ).erase (c+1) = {a,b,b+1} := by
      ext t
      simp
      omega
    rw [hf, show (c+1)-((c)-a)=a+1 by omega, orphan_plus_draw a b ha hab]
    decide
  · have he : ({a,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {a,b,b+1,c} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (c) (by simp) (by omega)
    have hf : ({a,b,b+1,c} : Finset ℕ).erase (c) = {a,b,b+1} := by
      ext t
      simp
      omega
    rw [hf, show (c)-((c+1)-a)=a-1 by omega, orphan_minus_draw a b ha hab hsep]
    decide

/-- Three actual adjacent pairs with minimum at least three are nonwinning. -/
theorem three_pairs_nonwin (a b c : ℕ)
    (ha : 3 ≤ a) (hab : a+2 ≤ b) (hbc : b+2 ≤ c) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},1⟩ ≠ .win := by
  apply nonwin_of_all_catching_children_nonloss _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (a) = {a+1,b,b+1,c,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
    have hf : ({a+1,b,b+1,c,c+1} : Finset ℕ).erase (a+1) = {b,b+1,c,c+1} := by
      ext t
      simp
      omega
    rw [hf, show (a+1)-((a)-1)=2 by omega]
    exact two_pairs_deficit_two_nonwin b c (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (a+1) = {a,b,b+1,c,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (a) (by simp) (by omega)
    have hf : ({a,b,b+1,c,c+1} : Finset ℕ).erase (a) = {b,b+1,c,c+1} := by
      ext t
      simp
      omega
    rw [hf, show (a)-((a+1)-1)=0 by omega]
    rw [position_value_zero_deficit_eq_value, two_pairs_tied_draw b c
      (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (b) = {a,a+1,b+1,c,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({a,a+1,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,a+1,c,c+1} := by
      ext t
      simp
      omega
    rw [hf, show (b+1)-((b)-1)=2 by omega]
    exact two_pairs_deficit_two_nonwin a c (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,a+1,b,c,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (b) (by simp) (by omega)
    have hf : ({a,a+1,b,c,c+1} : Finset ℕ).erase (b) = {a,a+1,c,c+1} := by
      ext t
      simp
      omega
    rw [hf, show (b)-((b+1)-1)=0 by omega]
    rw [position_value_zero_deficit_eq_value, two_pairs_tied_draw a c
      (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (c) = {a,a+1,b,b+1,c+1} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1} := by
      ext t
      simp
      omega
    rw [hf, show (c+1)-((c)-1)=2 by omega]
    exact two_pairs_deficit_two_nonwin a b (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,c} := by
      ext t
      simp
      omega
    rw [he]
    apply nonloss_of_catch _ _ (c) (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c} : Finset ℕ).erase (c) = {a,a+1,b,b+1} := by
      ext t
      simp
      omega
    rw [hf, show (c)-((c+1)-1)=0 by omega]
    rw [position_value_zero_deficit_eq_value, two_pairs_tied_draw a b
      (by omega) (by omega)]
    decide

/-- The separated three-pair endgame draws; no assumption about other game values is used. -/
theorem three_pairs_draw_of_separation (a b c : ℕ)
    (ha : 3 ≤ a) (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hsep : 2*a-1 ≤ b) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},1⟩ = .draw :=
  (Outcome.eq_draw_iff _).mpr
    ⟨three_pairs_nonloss_of_separation a b c (by omega) hab hbc hsep,
      three_pairs_nonwin a b c ha hab hbc⟩

/-- With the first pair three and four, arbitrary two higher adjacent pairs draw. -/
theorem three_pairs_anchor_three_draw (b c : ℕ) (hb : 5 ≤ b) (hbc : b+2 ≤ c) :
    Position.value ⟨{3,4,b,b+1,c,c+1},1⟩ = .draw := by
  exact three_pairs_draw_of_separation 3 b c (by omega) hb hbc (by omega)


/-- Below the separation threshold, the orphan-minus-one state wins by taking the pair's top. -/
theorem orphan_minus_win_of_close (a b : ℕ) (ha : 2 ≤ a) (hab : a+2 ≤ b)
    (hclose : b+2 ≤ 2*a) :
    Position.value ⟨{a,b,b+1},a-1⟩ = .win := by
  have he : ({a,b,b+1} : Finset ℕ).erase (b+1) = {a,b} := by ext x; simp; omega
  have hp : Position.value ⟨{a,b},b+1-(a-1)⟩ = .loss := by
    rw [CatchUpSearch.TopFourClassification.value_pair_exact a b (b+1-(a-1))
      (by omega) (by omega) (by omega)]
    change (if b+1-(a-1) < b-a then Outcome.win
      else if b+1-(a-1) = b-a then Outcome.draw
      else if b+1-(a-1) ≤ a then Outcome.loss
      else if b+1-(a-1) < a+b then Outcome.win
      else if b+1-(a-1) = a+b then Outcome.draw else Outcome.loss) = .loss
    simp [show ¬b+1-(a-1)<b-a by omega, show b+1-(a-1)≠b-a by omega,
      show b+1-(a-1)≤a by omega]
  have hmove : (⟨{a,b,b+1},a-1⟩ : Position).moveOutcome (b+1) = .win := by
    simp [Position.moveOutcome, Position.afterPick, show ¬b+1<a-1 by omega,
      he,hp,Outcome.neg]
  have hsum : b+1 ≤ ({a,b,b+1} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
  have hc : ¬ ({a,b,b+1} : Finset ℕ).sum id < a-1 := by omega
  by_contra hw
  rw [Position.value_eq_best_move_outcome _ (by simp) hc] at hw
  have hall := (Outcome.best_ne_win_iff _).mp hw
  exact hall .win (List.mem_map.mpr ⟨⟨b+1,by simp⟩,by simp,hmove⟩) rfl

/-- The one-pair orphan repair has an exact geometric threshold. -/
theorem orphan_minus_draw_iff (a b : ℕ) (ha : 2 ≤ a) (hab : a+2 ≤ b) :
    Position.value ⟨{a,b,b+1},a-1⟩ = .draw ↔ 2*a-1 ≤ b := by
  constructor
  · intro hd
    by_contra hsep
    have hw := orphan_minus_win_of_close a b ha hab (by omega)
    rw [hw] at hd
    cases hd
  · exact orphan_minus_draw a b ha hab

end CatchUp.AdjacentPairRepair
