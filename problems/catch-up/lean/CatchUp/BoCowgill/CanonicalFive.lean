/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/CanonicalFive.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.CanonicalFiveLeaves

/-!
# CanonicalFive

Necessary anchor conditions for a winning canonical five-pair deficit-three position; does not
assert every such position is nonwinning.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.CanonicalFive

open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (nonloss_of_continue)

/-- A uniform repair when deleting a pair exposes `(6,10,20,40)`.
For large q take6,10,20 in the same turn, then q+1. -/
theorem sparse_repair (q : ℕ) (hq : 8 ≤ q) (hqe : q%2=0)
    (hne : q≠10 ∧ q≠20 ∧ q≠40) :
    Position.value ⟨{6,7,10,11,20,21,40,41,q+1},q-3⟩ ≠ .loss := by
  by_cases hq42 : 42 ≤ q
  · have he : ({6,7,10,11,20,21,40,41,q+1} : Finset ℕ).erase 6 = {7,10,11,20,21,40,41,q+1} := by ext t; simp; omega
    have hf : ({7,10,11,20,21,40,41,q+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,q+1} := by ext t; simp; omega
    have hg : ({7,11,20,21,40,41,q+1} : Finset ℕ).erase 20 = {7,11,21,40,41,q+1} := by ext t; simp; omega
    have hh : ({7,11,21,40,41,q+1} : Finset ℕ).erase (q+1) = {7,11,21,40,41} := by ext t; simp; omega
    have hs : q+1 ≤ ({6,7,10,11,20,21,40,41,q+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
    rw [he,show q-3-6=q-9 by omega]
    have ht : q+1 ≤ ({7,10,11,20,21,40,41,q+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 10 (by simp) (by omega) (by omega)
    rw [hf,show q-9-10=q-19 by omega]
    have hu : q+1 ≤ ({7,11,20,21,40,41,q+1} : Finset ℕ).sum id :=
      Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
    apply nonloss_of_continue _ _ 20 (by simp) (by omega) (by omega)
    rw [hg,show q-19-20=q-39 by omega]
    apply nonloss_of_catch _ _ (q+1) (by simp) (by omega)
    rw [hh,show q+1-(q-39)=40 by omega,← Position.eval_eq_value]
    decide +kernel
  · by_cases hq8 : q=8
    · subst q
      exact sparse_eight_repair
    · have hs : q+1 ≤ ({6,7,10,11,20,21,40,41,q+1} : Finset ℕ).sum id :=
        Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
      have hq12 : 12 ≤ q := by omega
      apply nonloss_of_continue _ _ 6 (by simp) (by omega) (by omega)
      have he : ({6,7,10,11,20,21,40,41,q+1} : Finset ℕ).erase 6 = {7,10,11,20,21,40,41,q+1} := by ext t; simp; omega
      rw [he,show q-3-6=q-9 by omega]
      exact sparse_bounded_leaf q (by omega) hqe hne.2.1

private theorem orphan_nonloss (a b c e q : ℕ) (ha : 6 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e)
    (hae : a%2=0) (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0)
    (hq : 6 ≤ q) (hqe : q%2=0)
    (hqa : q+2 ≤ a ∨ a+2 ≤ q) (hqb : q+2 ≤ b ∨ b+2 ≤ q)
    (hqc : q+2 ≤ c ∨ c+2 ≤ q) (hqe' : q+2 ≤ e ∨ e+2 ≤ q) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1,q+1},q-3⟩ ≠ .loss := by
  by_cases hbad : a=6 ∧ b=10 ∧ c=20 ∧ e=40
  · obtain ⟨rfl,rfl,rfl,rfl⟩ := hbad
    exact sparse_repair q (by omega) hqe (by omega)
  apply nonloss_of_catch _ _ (q+1) (by simp) (by omega)
  have he : ({a,a+1,b,b+1,c,c+1,e,e+1,q+1} : Finset ℕ).erase (q+1) =
      {a,a+1,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
  rw [he,show q+1-(q-3)=4 by omega]
  exact CanonicalFour.four_four_nonwin a b c e ha hab hbc hce hae hbe hcc hee hbad

/-- Five canonical pairs at deficit three are nonwinning whenever their
minimum is at least six, with arbitrary magnitudes and gaps. -/
theorem five_three_nonwin_min_six (a b c e f : ℕ) (ha : 6 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f)
    (hae : a%2=0) (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0) (hfe : f%2=0) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1,f,f+1},3⟩ ≠ .win := by
  intro hw
  obtain ⟨x,hx,hloss⟩ := (FiveThree.five_three_win_iff_lower_loss a b c e f
    (by omega) hab hbc hce hef).mp hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx | hx <;> subst x
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase a = {b,b+1,c,c+1,e,e+1,f,f+1,a+1} := by ext t; simp; omega
    rw [he] at hloss
    exact orphan_nonloss b c e f a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hloss
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase b = {a,a+1,c,c+1,e,e+1,f,f+1,b+1} := by ext t; simp; omega
    rw [he] at hloss
    exact orphan_nonloss a c e f b (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hloss
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase c = {a,a+1,b,b+1,e,e+1,f,f+1,c+1} := by ext t; simp; omega
    rw [he] at hloss
    exact orphan_nonloss a b e f c (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hloss
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase e = {a,a+1,b,b+1,c,c+1,f,f+1,e+1} := by ext t; simp; omega
    rw [he] at hloss
    exact orphan_nonloss a b c f e (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hloss
  · have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase f = {a,a+1,b,b+1,c,c+1,e,e+1,f+1} := by ext t; simp; omega
    rw [he] at hloss
    exact orphan_nonloss a b c e f (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hloss

/-- Even with minimum four, the lowest lower-counter pick is never winning.
The one sparse boundary reserve has an explicit safe reply by twenty. -/
theorem lowest_lower_child_nonloss (a b c e f : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f)
    (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0) (hfe : f%2=0) :
    Position.value ⟨({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase a,a-3⟩ ≠ .loss := by
  have he : ({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase a =
      {a+1,b,b+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
  rw [he]
  by_cases hbad : b=6 ∧ c=10 ∧ e=20 ∧ f=40
  · obtain ⟨rfl,rfl,rfl,rfl⟩ := hbad
    have ha4 : a=4 := by omega
    subst a
    exact anchor_four_repair
  apply nonloss_of_catch _ _ (a+1) (by simp) (by omega)
  have hf : ({a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase (a+1) =
      {b,b+1,c,c+1,e,e+1,f,f+1} := by ext t; simp; omega
  rw [hf,show a+1-(a-3)=4 by omega]
  exact CanonicalFour.four_four_nonwin b c e f (by omega) hbc hce hef hbe hcc hee hfe hbad

/-- The remaining canonical five-pair problem is anchored at four and requires
one of the four nonminimal lower picks. The final reduction is symbolic;
prior lemmas use kernel-checked finite leaves. -/
theorem win_requires_anchor_four (a b c e f : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f)
    (hae : a%2=0) (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0) (hfe : f%2=0)
    (hw : Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1,f,f+1},3⟩ = .win) :
    a=4 ∧ ∃ x ∈ ({b,c,e,f} : Finset ℕ),
      Position.value ⟨({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase x,x-3⟩ = .loss := by
  have ha4 : a=4 := by
    by_contra hne
    exact five_three_nonwin_min_six a b c e f (by omega) hab hbc hce hef
      hae hbe hcc hee hfe hw
  obtain ⟨x,hx,hloss⟩ := (FiveThree.five_three_win_iff_lower_loss a b c e f
    ha hab hbc hce hef).mp hw
  have hxa : x≠a := by
    intro h
    subst x
    exact lowest_lower_child_nonloss a b c e f ha hab hbc hce hef hbe hcc hee hfe hloss
  refine ⟨ha4,x,?_,hloss⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx ⊢
  omega

end CatchUp.CanonicalFive
