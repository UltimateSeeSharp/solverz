/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/AnchorFive.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.AnchorFour

/-!
# AnchorFive

Five-pair restrictions and lower-orphan defenses when eight is absent; not an arbitrary-pair
induction.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.AnchorFour

open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (nonloss_of_continue)

/-- The four-first reply works for every orphan at least eight when the three
remaining canonical pairs omit eight. At six, the mate uses the four-pair theorem. -/
theorem lower_orphan_no_eight (b c e q : ℕ) (hb : 6 ≤ b)
    (hbc : b+2 ≤ c) (hce : c+2 ≤ e)
    (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0)
    (hbn : b≠8) (hcn : c≠8) (hen : e≠8)
    (hq : 6 ≤ q) (hqe : q%2=0)
    (hqb : q+2 ≤ b ∨ b+2 ≤ q) (hqc : q+2 ≤ c ∨ c+2 ≤ q)
    (hqe' : q+2 ≤ e ∨ e+2 ≤ q) :
    Position.value ⟨{4,5,b,b+1,c,c+1,e,e+1,q+1},q-3⟩ ≠ .loss := by
  by_cases hq6 : q=6
  · subst q
    apply nonloss_of_catch _ _ 7 (by simp) (by omega)
    have he : ({4,5,b,b+1,c,c+1,e,e+1,6+1} : Finset ℕ).erase 7 =
        {4,5,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
    rw [he]
    exact four_four_nonwin_no_eight b c e hb hbc hce hbe hcc hee hbn hcn hen
  have hq8 : 8 ≤ q := by omega
  have hs : q+1 ≤ ({4,5,b,b+1,c,c+1,e,e+1,q+1} : Finset ℕ).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) (by simp)
  apply nonloss_of_continue _ _ 4 (by simp) (by omega) (by omega)
  have he : ({4,5,b,b+1,c,c+1,e,e+1,q+1} : Finset ℕ).erase 4 =
      {5,b,b+1,c,c+1,e,e+1,q+1} := by ext t; simp; omega
  rw [he]
  apply nonloss_of_catch _ _ (q+1) (by simp) (by omega)
  have hf : ({5,b,b+1,c,c+1,e,e+1,q+1} : Finset ℕ).erase (q+1) =
      {5,b,b+1,c,c+1,e,e+1} := by ext t; simp; omega
  rw [hf,show q+1-(q-3-4)=8 by omega]
  exact five_three_pairs_eight b c e hb hbc hce hbe hcc hee hbn hcn hen

/-- All four nonminimal lower picks are safe for the defender when eight is absent. -/
theorem anchored_five_three_nonwin_no_eight (b c e f : ℕ) (hb : 6 ≤ b)
    (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f)
    (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0) (hfe : f%2=0)
    (hbn : b≠8) (hcn : c≠8) (hen : e≠8) (hfn : f≠8) :
    Position.value ⟨{4,5,b,b+1,c,c+1,e,e+1,f,f+1},3⟩ ≠ .win := by
  intro hw
  obtain ⟨_,x,hx,hloss⟩ := CanonicalFive.win_requires_anchor_four 4 b c e f
    (by omega) (by omega) hbc hce hef (by omega) hbe hcc hee hfe hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  · have he : ({4,5,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase b =
        {4,5,c,c+1,e,e+1,f,f+1,b+1} := by ext t; simp; omega
    rw [he] at hloss
    exact lower_orphan_no_eight c e f b (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hloss
  · have he : ({4,5,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase c =
        {4,5,b,b+1,e,e+1,f,f+1,c+1} := by ext t; simp; omega
    rw [he] at hloss
    exact lower_orphan_no_eight b e f c (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hloss
  · have he : ({4,5,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase e =
        {4,5,b,b+1,c,c+1,f,f+1,e+1} := by ext t; simp; omega
    rw [he] at hloss
    exact lower_orphan_no_eight b c f e (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hloss
  · have he : ({4,5,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase f =
        {4,5,b,b+1,c,c+1,e,e+1,f+1} := by ext t; simp; omega
    rw [he] at hloss
    exact lower_orphan_no_eight b c e f (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hloss

/-- Canonical five-pair wins require a counter eight, for any minimum at least four. -/
theorem five_three_nonwin_no_eight (a b c e f : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f)
    (hae : a%2=0) (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0) (hfe : f%2=0)
    (hno : 8 ∉ ({a,b,c,e,f} : Finset ℕ)) :
    Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1,f,f+1},3⟩ ≠ .win := by
  by_cases ha4 : a=4
  · subst a
    simp only [Finset.mem_insert,Finset.mem_singleton] at hno
    exact anchored_five_three_nonwin_no_eight b c e f (by omega) hbc hce hef
      hbe hcc hee hfe (by omega) (by omega) (by omega) (by omega)
  exact CanonicalFive.five_three_nonwin_min_six a b c e f (by omega) hab hbc hce hef
    hae hbe hcc hee hfe

/-- The lower pick eight is safe in both possible sorted locations. -/
theorem lower_eight_child_nonloss (b c e f : ℕ) (hb : 6 ≤ b)
    (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f)
    (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0) (hfe : f%2=0)
    (h8 : 8 ∈ ({b,c,e,f} : Finset ℕ)) :
    Position.value ⟨({4,5,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase 8,5⟩ ≠ .loss := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at h8
  rcases h8 with hb8 | hc8 | he8 | hf8
  · have he : ({4,5,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase 8 =
        {4,5,c,c+1,e,e+1,f,f+1,9} := by ext t; simp; omega
    rw [he]
    exact lower_orphan_no_eight c e f 8 (by omega) hce hef hcc hee hfe
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · have he : ({4,5,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase 8 =
        {4,5,b,b+1,e,e+1,f,f+1,9} := by ext t; simp; omega
    rw [he]
    exact lower_orphan_no_eight b e f 8 hb (by omega) hef hbe hee hfe
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · omega
  · omega

/-- Any unresolved canonical win uses both anchor pairs and a different lower pick. -/
theorem win_requires_four_and_eight (a b c e f : ℕ) (ha : 4 ≤ a)
    (hab : a+2 ≤ b) (hbc : b+2 ≤ c) (hce : c+2 ≤ e) (hef : e+2 ≤ f)
    (hae : a%2=0) (hbe : b%2=0) (hcc : c%2=0) (hee : e%2=0) (hfe : f%2=0)
    (hw : Position.value ⟨{a,a+1,b,b+1,c,c+1,e,e+1,f,f+1},3⟩ = .win) :
    a=4 ∧ 8 ∈ ({b,c,e,f} : Finset ℕ) ∧
      ∃ x ∈ ({b,c,e,f} : Finset ℕ), x≠8 ∧
        Position.value ⟨({a,a+1,b,b+1,c,c+1,e,e+1,f,f+1} : Finset ℕ).erase x,x-3⟩ = .loss := by
  obtain ⟨ha4,x,hx,hloss⟩ := CanonicalFive.win_requires_anchor_four a b c e f
    ha hab hbc hce hef hae hbe hcc hee hfe hw
  have h8 : 8 ∈ ({b,c,e,f} : Finset ℕ) := by
    by_contra hn
    have hno : 8 ∉ ({a,b,c,e,f} : Finset ℕ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hn ⊢
      omega
    exact five_three_nonwin_no_eight a b c e f ha hab hbc hce hef
      hae hbe hcc hee hfe hno hw
  have hx8 : x≠8 := by
    intro he
    subst x
    subst a
    exact lower_eight_child_nonloss b c e f (by omega) hbc hce hef hbe hcc hee hfe h8 hloss
  exact ⟨ha4,h8,x,hx,hx8,hloss⟩

end CatchUp.AnchorFour
