/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/FiveThree.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.DeficitTwo

/-!
# FiveThree

Refutes an unrestricted five-pair deficit-three principle, while proving safe upper-move reductions.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.FiveThree

open CatchUp.DeficitTwo (win_of_catch)
open CatchUp.DeficitTwo (nonloss_of_move)
open CatchUp.DeficitTwo (nonloss_of_catch)

/-- The child after taking `14` is losing under optimal outcome play. -/
theorem sparse_child_loss :
    Position.value ⟨{4,5,7,8,15,23,24,31,32},11⟩ = .loss := by
  rw [← Position.eval_eq_value]
  decide +kernel

/-- Counterexample to uniform five-pair deficit-three nonwinning.
This is an auxiliary normalized-state claim, not a refutation of Catch-Up. -/
theorem sparse_five_pairs_win :
    Position.value ⟨{4,5,7,8,14,15,23,24,31,32},3⟩ = .win := by
  have he : ({4,5,7,8,14,15,23,24,31,32} : Finset ℕ).erase 14 =
      {4,5,7,8,15,23,24,31,32} := by decide +kernel
  apply win_of_catch _ _ 14 (by decide +kernel) (by omega)
  rw [he,show 14-3=11 by omega,sparse_child_loss]

/-- Every legal defender pick at the losing child has losing move outcome.
This quantifies over all picks, including the four below the deficit. -/
theorem sparse_every_reply_loses (x : ℕ)
    (hx : x ∈ ({4,5,7,8,15,23,24,31,32} : Finset ℕ)) :
    (⟨{4,5,7,8,15,23,24,31,32},11⟩ : Position).moveOutcome x = .loss := by
  by_contra hn
  have hs : 32 ≤ ({4,5,7,8,15,23,24,31,32} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by decide +kernel)
  exact (nonloss_of_move _ _ x hx (by omega) hn) sparse_child_loss

/-- The proposed uniform arbitrary-support five-pair reserve invariant is false. -/
theorem not_uniform_five_three : ¬ (∀ a b c e f : ℕ, 4 ≤ a →
    a+2 ≤ b → b+2 ≤ c → c+2 ≤ e → e+2 ≤ f →
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1,f,f+1},3⟩ ≠ .win) := by
  intro h
  exact h 4 7 14 23 31 (by omega) (by omega) (by omega) (by omega)
    (by omega) sparse_five_pairs_win


/-- The certified win also holds in the literal absolute-score reference evaluator. -/
theorem sparse_reference_win :
    valueAux {4,5,7,8,14,15,23,24,31,32} 0 3 false = .win := by
  rw [← Position.value_eq_value_aux _ 0 3 (by omega)]
  exact sparse_five_pairs_win

/-- Every upper-counter pick has a nonlosing mate response, for arbitrary gaps. -/
theorem upper_move_nonwin (a b c e f x : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f)
    (hx : x ∈ ({a+1,b+1,c+1,e+1,f+1} : Finset ℕ)) :
    (⟨{a,a+1,b,b+1,c,c+1,e,e+1,f,f+1},3⟩ : Position).moveOutcome x ≠ .win := by
  have hc : 3 ≤ x := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    omega
  simp only [Position.moveOutcome,Position.afterPick,not_lt_of_ge hc,
    ite_false,Outcome.neg_ne_win_iff]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (a+1) = {a,b,b+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ a (by simp) (by omega)
    have hf : ({a,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase a = {b,b+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [hf,show a-(a+1-3)=2 by omega]
    exact DeficitTwo.four_pairs_two_nonwin b c e f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (b+1) = {a,a+1,b,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ b (by simp) (by omega)
    have hf : ({a,a+1,b,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase b = {a,a+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [hf,show b-(b+1-3)=2 by omega]
    exact DeficitTwo.four_pairs_two_nonwin a c e f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (c+1) = {a,a+1,b,b+1,c,e,e+1,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ c (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,e,e+1,f,f+1} : Finset ℕ).erase c = {a,a+1,b,b+1,e,e+1,f,f+1} := by ext t; simp; omega
    rw [hf,show c-(c+1-3)=2 by omega]
    exact DeficitTwo.four_pairs_two_nonwin a b e f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (e+1) = {a,a+1,b,b+1,c,c+1,e,f,f+1} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ e (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,c+1,e,f,f+1} : Finset ℕ).erase e = {a,a+1,b,b+1,c,c+1,f,f+1} := by ext t; simp; omega
    rw [hf,show e-(e+1-3)=2 by omega]
    exact DeficitTwo.four_pairs_two_nonwin a b c f (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (f+1) = {a,a+1,b,b+1,c,c+1,e,e+1,f} := by ext t; simp; omega
    rw [he]
    apply nonloss_of_catch _ _ f (by simp) (by omega)
    have hf : ({a,a+1,b,b+1,c,c+1,e,e+1,f} : Finset ℕ).erase f = {a,a+1,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [hf,show f-(f+1-3)=2 by omega]
    exact DeficitTwo.four_pairs_two_nonwin a b c e (by omega) (by omega) (by omega) (by omega)



/-- Only a lower-counter pick can witness a five-pair win at deficit three.
This leaves five precisely specified losing-child obligations for future search. -/
theorem five_three_win_iff_lower_loss (a b c e f : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1,f,f+1},3⟩ = .win ↔
      ∃ x ∈ ({a,b,c,e,f} : Finset ℕ),
        Position.value ⟨({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase x,x-3⟩ = .loss := by
  have hs : a ≤ ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
  rw [CatchUpSearch.TopFourClassification.value_eq_win_iff _ (by simp) (by change ¬ ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).sum id < 3; omega)]
  constructor
  · rintro ⟨x,hx,hm⟩
    have hu : x ∉ ({a+1,b+1,c+1,e+1,f+1} : Finset ℕ) := by
      intro hupper
      exact upper_move_nonwin a b c e f x ha hab hbc hce hef hupper hm
    have hl : x ∈ ({a,b,c,e,f} : Finset ℕ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx hu ⊢
      omega
    have hc : 3 ≤ x := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hl
      omega
    refine ⟨x,hl,?_⟩
    by_contra hn
    have hnot : (⟨{a,a+1,b,b+1,c,c+1,e,e+1,f,f+1},3⟩ : Position).moveOutcome x ≠ .win := by
      simpa only [Position.moveOutcome,Position.afterPick,not_lt_of_ge hc,
        ite_false,Outcome.neg_ne_win_iff] using hn
    exact hnot hm
  · rintro ⟨x,hx,hloss⟩
    have hm : x ∈ ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
      omega
    have hc : 3 ≤ x := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      omega
    refine ⟨x,hm,?_⟩
    simp only [Position.moveOutcome,Position.afterPick,not_lt_of_ge hc,
      ite_false,hloss,Outcome.neg]

end CatchUp.FiveThree
