/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DeficitTwo.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates.
-/
module

public import Mathlib
public import CatchUp.AdjacentPairGeometryRepair
public import CatchUp.Increasing

/-!
# Deficit-two paired endgames

The objective is nonwinning for `[4,N]` at deficit two. This file proves a
parameterized four-pair fragment, with every opposing pick quantified over.
It does not assert closure for arbitrary numbers of pairs.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.DeficitTwo

theorem nonloss_of_move (S : Finset ℕ) (d x : ℕ) (hx : x ∈ S)
    (hc : d ≤ S.sum id) (hm : (⟨S,d⟩ : Position).moveOutcome x ≠ .loss) :
    Position.value ⟨S,d⟩ ≠ .loss := by
  rw [Position.value_eq_best_move_outcome _
    (Finset.nonempty_iff_ne_empty.mp ⟨x,hx⟩) (by exact Nat.not_lt.mpr hc)]
  exact (Outcome.best_ne_loss_iff _).mpr
    ⟨_,List.mem_map.mpr ⟨⟨x,hx⟩,by simp,rfl⟩,hm⟩

theorem win_of_move (S : Finset ℕ) (d x : ℕ) (hx : x ∈ S)
    (hc : d ≤ S.sum id) (hm : (⟨S,d⟩ : Position).moveOutcome x = .win) :
    Position.value ⟨S,d⟩ = .win := by
  by_contra hn
  rw [Position.value_eq_best_move_outcome _
    (Finset.nonempty_iff_ne_empty.mp ⟨x,hx⟩) (by exact Nat.not_lt.mpr hc)] at hn
  exact (Outcome.best_ne_win_iff _).mp hn _
    (List.mem_map.mpr ⟨⟨x,hx⟩,by simp,rfl⟩) hm

theorem win_of_catch (S : Finset ℕ) (d x : ℕ)
    (hx : x ∈ S) (hd : d ≤ x)
    (hl : Position.value ⟨S.erase x,x-d⟩ = .loss) :
    Position.value ⟨S,d⟩ = .win := by
  apply win_of_move S d x hx
    (hd.trans (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx))
  simp [Position.moveOutcome, Position.afterPick, not_lt_of_ge hd, hl, Outcome.neg]

theorem nonloss_of_catch (S : Finset ℕ) (d x : ℕ)
    (hx : x ∈ S) (hd : d ≤ x)
    (hn : Position.value ⟨S.erase x,x-d⟩ ≠ .win) :
    Position.value ⟨S,d⟩ ≠ .loss := by
  apply nonloss_of_move S d x hx
    (hd.trans (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx))
  simpa only [Position.moveOutcome, Position.afterPick, not_lt_of_ge hd,
    ite_false, Outcome.neg_ne_loss_iff] using hn

theorem nonloss_of_continue (S : Finset ℕ) (d x : ℕ)
    (hx : x ∈ S) (hd : x < d) (hc : d ≤ S.sum id)
    (hn : Position.value ⟨S.erase x,d-x⟩ ≠ .loss) :
    Position.value ⟨S,d⟩ ≠ .loss := by
  apply nonloss_of_move S d x hx hc
  simpa only [Position.moveOutcome, Position.afterPick, hd, ite_true] using hn

theorem all_catching (S : Finset ℕ) (d : ℕ)
    (hne : S.Nonempty) (hc : ∀ x ∈ S, d ≤ x)
    (hn : ∀ x ∈ S, Position.value ⟨S.erase x,x-d⟩ ≠ .loss) :
    Position.value ⟨S,d⟩ ≠ .win := by
  obtain ⟨x,hx⟩ := hne
  have hsum : x ≤ S.sum id := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  rw [Position.value_eq_best_move_outcome _
    (Finset.nonempty_iff_ne_empty.mp ⟨x,hx⟩) (by exact Nat.not_lt.mpr ((hc x hx).trans hsum))]
  apply (Outcome.best_ne_win_iff _).mpr
  intro o ho
  obtain ⟨⟨y,hy⟩,_,rfl⟩ := List.mem_map.mp ho
  simpa only [Position.moveOutcome, Position.afterPick, not_lt_of_ge (hc y hy),
    ite_false, Outcome.neg_ne_win_iff] using hn y hy

theorem adjacent_pair_loss (a d : ℕ) (hd : 1 < d) (ha : d ≤ a) :
    Position.value ⟨{a,a+1},d⟩ = .loss := by
  rw [CatchUpSearch.TopFourClassification.value_pair_exact a (a+1) d
    (by omega) (by omega) (by omega)]
  change (if d < a+1-a then Outcome.win else if d = a+1-a then Outcome.draw
    else if d ≤ a then Outcome.loss else if d < a+(a+1) then Outcome.win
    else if d = a+(a+1) then Outcome.draw else Outcome.loss) = .loss
  simp [show a+1-a=1 by omega, show ¬d<1 by omega, show d≠1 by omega, ha]

/-- The only excluded deficit-four two-pair geometries with minimum at least four
are `{4,5,7,8}` and `{4,5,8,9}`. Both exclusions are necessary. -/
theorem two_pairs_four_nonwin (a b : ℕ) (ha : 4 ≤ a) (hab : a+2 ≤ b)
    (hex : a = 4 → b ≠ 7 ∧ b ≠ 8) :
    Position.value ⟨{a,a+1,b,b+1},4⟩ ≠ .win := by
  by_cases hsmall : a = 4 ∧ b = 6
  · obtain ⟨rfl,rfl⟩ := hsmall
    rw [← Position.eval_eq_value]
    decide +kernel
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase a = {a+1,b,b+1} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
    have hf : ({a+1,b,b+1} : Finset ℕ).erase (a+1) = {b,b+1} := by
      ext t; simp; omega
    rw [hf, show a+1-(a-4)=5 by omega, adjacent_pair_loss b 5 (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase (a+1) = {a,b,b+1} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ a (by simp) (by omega)
    have hf : ({a,b,b+1} : Finset ℕ).erase a = {b,b+1} := by
      ext t; simp; omega
    rw [hf, show a-(a+1-4)=3 by omega, adjacent_pair_loss b 3 (by omega) (by omega)]
    decide
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase b = {a,a+1,b+1} := by
      ext t; simp; omega
    rw [he]
    by_cases ha5 : 5 ≤ a
    · apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({a,a+1,b+1} : Finset ℕ).erase (b+1) = {a,a+1} := by
        ext t; simp; omega
      rw [hf, show b+1-(b-4)=5 by omega, adjacent_pair_loss a 5 (by omega) ha5]
      decide
    · have ha4 : a = 4 := by omega
      subst a
      have hb : 9 ≤ b := by have := hex rfl; omega
      have hf : ({4,5,b+1} : Finset ℕ).erase 4 = {5,b+1} := by
        ext t; simp; omega
      have hg : ({5,b+1} : Finset ℕ).erase (b+1) = {5} := by
        ext t; simp; omega
      have hl : Position.value ⟨{5},9⟩ = .loss := by
        rw [← Position.eval_eq_value]; decide +kernel
      have hw : Position.value ⟨{5,b+1},b-8⟩ = .win := by
        apply win_of_catch _ _ (b+1) (by simp) (by omega)
        rw [hg, show b+1-(b-8)=9 by omega, hl]
      have hsum : b+1 ≤ ({4,5,b+1} : Finset ℕ).sum id :=
        Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
      apply nonloss_of_move _ _ 4 (by simp)
        (by change b-4 ≤ ({4,5,b+1} : Finset ℕ).sum id; omega)
      simpa only [Position.moveOutcome, Position.afterPick, show 4 < b-4 by omega,
        ite_true, hf, show b-4-4=b-8 by omega, hw] using (by decide : Outcome.win ≠ .loss)
  · have he : ({a,a+1,b,b+1} : Finset ℕ).erase (b+1) = {a,a+1,b} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({a,a+1,b} : Finset ℕ).erase b = {a,a+1} := by
      ext t; simp; omega
    rw [hf, show b-(b+1-4)=3 by omega, adjacent_pair_loss a 3 (by omega) (by omega)]
    decide

private theorem seven_gap_repair (c : ℕ) (hc : 9 ≤ c) (hex : c ≠ 14) :
    Position.value ⟨{4,5,7,8,c+1},c-3⟩ ≠ .loss := by
  by_cases hc15 : 15 ≤ c
  · have he : ({4,5,7,8,c+1} : Finset ℕ).erase 4 = {5,7,8,c+1} := by
      ext t; simp; omega
    have hf : ({5,7,8,c+1} : Finset ℕ).erase 7 = {5,8,c+1} := by
      ext t; simp; omega
    have hg : ({5,8,c+1} : Finset ℕ).erase (c+1) = {5,8} := by
      ext t; simp; omega
    have hl : Position.value ⟨{5,8},15⟩ = .loss := by
      rw [← Position.eval_eq_value]; decide +kernel
    have hsum : c+1 ≤ ({4,5,7,8,c+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 4 (by simp) (by omega) (by omega)
    rw [he, show c-3-4=c-7 by omega]
    have hsum' : c+1 ≤ ({5,7,8,c+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 7 (by simp) (by omega) (by omega)
    rw [hf, show c-7-7=c-14 by omega]
    apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
    rw [hg, show c+1-(c-14)=15 by omega, hl]
    decide
  · have hc13 : c ≤ 13 := by omega
    interval_cases c <;> rw [← Position.eval_eq_value] <;> decide +kernel

/-- A three-pair deficit-three reserve has precisely one possible winning
geometry with minimum at least four: the starts `4,7,14`. -/
theorem three_pairs_three_nonwin (a b c : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hex : ¬ (a = 4 ∧ b = 7 ∧ c = 14)) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},3⟩ ≠ .win := by
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase a = {a+1,b,b+1,c,c+1} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
    have hf : ({a+1,b,b+1,c,c+1} : Finset ℕ).erase (a+1) = {b,b+1,c,c+1} := by
      ext t; simp; omega
    rw [hf, show a+1-(a-3)=4 by omega]
    exact two_pairs_four_nonwin b c (by omega) hbc (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (a+1) = {a,b,b+1,c,c+1} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ a (by simp) (by omega)
    have hf : ({a,b,b+1,c,c+1} : Finset ℕ).erase a = {b,b+1,c,c+1} := by
      ext t; simp; omega
    rw [hf, show a-(a+1-3)=2 by omega]
    exact AdjacentPairRepair.two_pairs_deficit_two_nonwin b c (by omega) hbc
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase b = {a,a+1,b+1,c,c+1} := by
      ext t; simp; omega
    rw [he]
    by_cases hexc : a = 4 ∧ c = 8
    · obtain ⟨rfl,rfl⟩ := hexc
      have hb : b = 6 := by omega
      subst b
      rw [← Position.eval_eq_value]
      decide +kernel
    · apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
      have hf : ({a,a+1,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,a+1,c,c+1} := by
        ext t; simp; omega
      rw [hf, show b+1-(b-3)=4 by omega]
      exact two_pairs_four_nonwin a c ha (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (b+1) = {a,a+1,b,c,c+1} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({a,a+1,b,c,c+1} : Finset ℕ).erase b = {a,a+1,c,c+1} := by
      ext t; simp; omega
    rw [hf, show b-(b+1-3)=2 by omega]
    exact AdjacentPairRepair.two_pairs_deficit_two_nonwin a c (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase c = {a,a+1,b,b+1,c+1} := by
      ext t; simp; omega
    rw [he]
    by_cases hexb : a = 4 ∧ b = 8
    · obtain ⟨rfl,rfl⟩ := hexb
      have hc : 10 ≤ c := by omega
      have hf : ({4,5,8,9,c+1} : Finset ℕ).erase 4 = {5,8,9,c+1} := by
        ext t; simp; omega
      have hg : ({5,8,9,c+1} : Finset ℕ).erase (c+1) = {5,8,9} := by
        ext t; simp; omega
      have hl : Position.value ⟨{5,8,9},8⟩ = .loss := by
        rw [← Position.eval_eq_value]; decide +kernel
      have hw : Position.value ⟨{5,8,9,c+1},c-7⟩ = .win := by
        apply win_of_catch _ _ (c+1) (by simp) (by omega)
        rw [hg, show c+1-(c-7)=8 by omega, hl]
      have hsum : c+1 ≤ ({4,5,8,9,c+1} : Finset ℕ).sum id :=
        Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
      apply nonloss_of_move _ _ 4 (by simp)
        (by change c-3 ≤ ({4,5,8,9,c+1} : Finset ℕ).sum id; omega)
      simpa only [Position.moveOutcome, Position.afterPick, show 4<c-3 by omega,
        ite_true, hf, show c-3-4=c-7 by omega, hw] using (by decide : Outcome.win ≠ .loss)
    · by_cases hexb7 : a = 4 ∧ b = 7
      · obtain ⟨rfl,rfl⟩ := hexb7
        exact seven_gap_repair c (by omega) (by omega)
      · apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
        have hf : ({a,a+1,b,b+1,c+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1} := by
          ext t; simp; omega
        rw [hf, show c+1-(c-3)=4 by omega]
        exact two_pairs_four_nonwin a b ha hab (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,c} := by
      ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ c (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c} : Finset ℕ).erase c = {a,a+1,b,b+1} := by
      ext t; simp; omega
    rw [hf, show c-(c+1-3)=2 by omega]
    exact AdjacentPairRepair.two_pairs_deficit_two_nonwin a b (by omega) hab

/-- The unique strict-win geometry in the three-pair deficit-three family. -/
theorem three_pairs_three_win_iff (a b c : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1},3⟩ = .win ↔ a = 4 ∧ b = 7 ∧ c = 14 := by
  constructor
  · intro hw
    by_contra hex
    exact three_pairs_three_nonwin a b c ha hab hbc hex hw
  · rintro ⟨rfl,rfl,rfl⟩
    rw [← Position.eval_eq_value]
    decide +kernel

private theorem four_pair_exception_repair (f : ℕ) (hf : 9 ≤ f)
    (hgap : f ≤ 12 ∨ 16 ≤ f) :
    Position.value ⟨{4,5,7,8,14,15,f+1},f-2⟩ ≠ .loss := by
  rcases hgap with hsmall | hlarge
  · interval_cases f <;> rw [← Position.eval_eq_value] <;> decide +kernel
  · have he : ({4,5,7,8,14,15,f+1} : Finset ℕ).erase 4 = {5,7,8,14,15,f+1} := by
      ext t; simp; omega
    have hh : ({5,7,8,14,15,f+1} : Finset ℕ).erase 7 = {5,8,14,15,f+1} := by
      ext t; simp; omega
    have hg : ({5,8,14,15,f+1} : Finset ℕ).erase (f+1) = {5,8,14,15} := by
      ext t; simp; omega
    have hd : Position.value ⟨{5,8,14,15},14⟩ = .draw := by
      rw [← Position.eval_eq_value]; decide +kernel
    have hsum : f+1 ≤ ({4,5,7,8,14,15,f+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 4 (by simp) (by omega) (by omega)
    rw [he, show f-2-4=f-6 by omega]
    have hsum' : f+1 ≤ ({5,7,8,14,15,f+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 7 (by simp) (by omega) (by omega)
    rw [hh, show f-6-7=f-13 by omega]
    apply nonloss_of_catch _ _ (f+1) (by simp) (by omega)
    rw [hg, show f+1-(f-13)=14 by omega, hd]
    decide

/-- Four disjoint adjacent pairs are nonwinning at deficit two, with arbitrary
gaps and minimum at least four.

Answer each first pick by its mate, leaving three pairs and deficit three
(lower pick) or one (upper pick). If this would expose the unique winning
triple, use the explicit repair above instead. All eight picks are covered. -/
theorem four_pairs_two_nonwin (a b c e : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1},2⟩ ≠ .win := by
  apply all_catching _ _ ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase a =
        {a+1,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
    have hf : ({a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a+1) =
        {b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf, show a+1-(a-2)=3 by omega]
    exact three_pairs_three_nonwin b c e (by omega) hbc hce (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (a+1) =
        {a,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ a (by simp) (by omega)
    have hf : ({a,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase a =
        {b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf, show a-(a+1-2)=1 by omega]
    exact AdjacentPairRepair.three_pairs_nonwin b c e (by omega) hbc hce
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase b =
        {a,a+1,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ (b+1) (by simp) (by omega)
    have hf : ({a,a+1,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b+1) =
        {a,a+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf, show b+1-(b-2)=3 by omega]
    exact three_pairs_three_nonwin a c e ha (by omega) hce (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (b+1) =
        {a,a+1,b,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({a,a+1,b,c,c+1,e,e+1} : Finset ℕ).erase b =
        {a,a+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf, show b-(b+1-2)=1 by omega]
    exact AdjacentPairRepair.three_pairs_nonwin a c e (by omega) (by omega) hce
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase c =
        {a,a+1,b,b+1,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    by_cases hex : a = 4 ∧ b = 7 ∧ e = 14
    · obtain ⟨rfl,rfl,rfl⟩ := hex
      have hs : ({4,4+1,7,7+1,c+1,14,14+1} : Finset ℕ) =
          {4,5,7,8,14,15,c+1} := by
        ext t
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      rw [hs]
      exact four_pair_exception_repair c (by omega) (Or.inl (by omega))
    · apply nonloss_of_catch _ _ (c+1) (by simp) (by omega)
      have hf : ({a,a+1,b,b+1,c+1,e,e+1} : Finset ℕ).erase (c+1) =
          {a,a+1,b,b+1,e,e+1} := by ext t; simp; omega
      rw [hf, show c+1-(c-2)=3 by omega]
      exact three_pairs_three_nonwin a b e ha hab (by omega) hex
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (c+1) =
        {a,a+1,b,b+1,c,e,e+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ c (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,e,e+1} : Finset ℕ).erase c =
        {a,a+1,b,b+1,e,e+1} := by ext t; simp; omega
    rw [hf, show c-(c+1-2)=1 by omega]
    exact AdjacentPairRepair.three_pairs_nonwin a b e (by omega) hab (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase e =
        {a,a+1,b,b+1,c,c+1,e+1} := by ext t; simp; omega
    rw [he]
    by_cases hex : a = 4 ∧ b = 7 ∧ c = 14
    · obtain ⟨rfl,rfl,rfl⟩ := hex
      exact four_pair_exception_repair e (by omega) (Or.inr hce)
    · apply nonloss_of_catch _ _ (e+1) (by simp) (by omega)
      have hf : ({a,a+1,b,b+1,c,c+1,e+1} : Finset ℕ).erase (e+1) =
          {a,a+1,b,b+1,c,c+1} := by ext t; simp; omega
      rw [hf, show e+1-(e-2)=3 by omega]
      exact three_pairs_three_nonwin a b c ha hab hbc hex
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1} : Finset ℕ).erase (e+1) =
        {a,a+1,b,b+1,c,c+1,e} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ e (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,c+1,e} : Finset ℕ).erase e =
        {a,a+1,b,b+1,c,c+1} := by ext t; simp; omega
    rw [hf, show e-(e+1-2)=1 by omega]
    exact AdjacentPairRepair.three_pairs_nonwin a b c (by omega) hab hbc

/-- An infinite family of translated intervals, of fixed width eight. This is
not a theorem about intervals of arbitrary length. -/
theorem interval_eight_nonwin (a : ℕ) (ha : 4 ≤ a) :
    Position.value ⟨Finset.Icc a (a+7),2⟩ ≠ .win := by
  have hs : Finset.Icc a (a+7) =
      {a,a+1,a+2,(a+2)+1,a+4,(a+4)+1,a+6,(a+6)+1} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [hs]
  exact four_pairs_two_nonwin a (a+2) (a+4) (a+6) ha (by omega) (by omega) (by omega)

/-- The requested interval family at eleven follows from the symbolic proof. -/
theorem interval_eleven_nonwin : Position.value ⟨Finset.Icc 4 11,2⟩ ≠ .win :=
  interval_eight_nonwin 4 (by omega)

/-- Deficit-two nonwinning suffices for the first-pair player's nonloss:
take `3`, ending the turn immediately. The opposite nonloss direction is a
separate obligation. -/
theorem first_pair_nonloss_of_interval_nonwin (N : ℕ) (hN : 3 ≤ N)
    (hn : Position.value ⟨Finset.Icc 4 N,2⟩ ≠ .win) :
    Position.value ⟨Finset.Icc 3 N,1⟩ ≠ .loss := by
  apply nonloss_of_catch _ _ 3 (by simp; omega) (by omega)
  have hs : (Finset.Icc 3 N).erase 3 = Finset.Icc 4 N := by
    ext x; simp; omega
  simpa only [hs] using hn

/-- This deficit-two interval is an actual reachable post-opening position,
after the legal picks `1,2,3`, with Player 2 next. -/
theorem interval_reachable (N : ℕ) (hN : 3 ≤ N) :
    ReachableFromOpening N 1 ⟨⟨Finset.Icc 4 N,2⟩,.p2⟩ := by
  let p : GamePosition := ⟨⟨Finset.Icc 3 N,1⟩,.p1⟩
  have hx : p.LegalMove 3 := by change 3 ∈ Finset.Icc 3 N; simp; omega
  have hsum : 3 ≤ p.remaining.sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  have ht : ¬ p.IsTerminal := by
    apply (GamePosition.not_is_terminal_iff p).mpr
    exact ⟨Finset.nonempty_iff_ne_empty.mp ⟨3,hx⟩,
      by change ¬ p.remaining.sum id < 1; omega⟩
  have hr : ReachableFromOpening N 1 p := Increasing.first_pair_reachable N (by omega)
  have he : (Finset.Icc 3 N).erase 3 = Finset.Icc 4 N := by ext x; simp; omega
  simpa [p, GamePosition.afterPick, Position.afterPick, he, Player.other] using
    hr.after_pick 3 ht hx

end CatchUp.DeficitTwo
