/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/UniformExactSumDescentObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.ExactSumLossObstruction

/-!
# An obstruction to upper-only exact-sum descent

At opening `m+4`, every exact block that permits only original upper witnesses
must be `{4,m}`. The next structurally permitted opening `m+3` admits no
such block. These statements hold for every `m ≥ 6` and `k ≥ 2`.

This is a restriction on a precisely specified proof grammar. It does not say
that the permitted branch is actually losing, nor that uniform nonloss is false.
Additional semantic exclusions or lower-witness repairs are outside this grammar.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.UniformExactSumDescent

/-- The tied support left by deleting one and two consecutive counters. -/
def support (m k : ℕ) : Finset ℕ := Finset.Icc 2 m ∪ Finset.Icc (m+3) (m+k+2)

/-- Every witness allowed solely by membership and the strict block bound is upper. -/
def UpperOnly (S A : Finset ℕ) (m : ℕ) : Prop :=
  ∀ w ∈ S \ A, (∀ a ∈ A, a < w) → m+3 ≤ w

private theorem sum_ne_one_of_min_two (A : Finset ℕ)
    (hmin : ∀ x ∈ A, 2 ≤ x) : A.sum id ≠ 1 := by
  intro hs
  by_cases he : A = ∅
  · simp [he] at hs
  obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hle : x ≤ A.sum id := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  have := hmin x hx
  omega

private theorem sum_four_unique (A : Finset ℕ)
    (hmin : ∀ x ∈ A, 2 ≤ x) (hs : A.sum id = 4) : A = {4} := by
  have hsub : A ⊆ ({2,3,4} : Finset ℕ) := by
    intro x hx
    have hle : x ≤ A.sum id := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
    have := hmin x hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have finite_check : ∀ B ∈ ({2,3,4} : Finset ℕ).powerset,
      B.sum id = 4 → B = {4} := by decide +kernel
  exact finite_check A (Finset.mem_powerset.mpr hsub) hs

private theorem upper_only_forces_max (S A : Finset ℕ) (m : ℕ)
    (hm : m ∈ S) (hbound : ∀ a ∈ A, a ≤ m) (hu : UpperOnly S A m) :
    m ∈ A := by
  by_contra hma
  have hw := hu m (Finset.mem_sdiff.mpr ⟨hm,hma⟩) (by
    intro a ha
    have hle := hbound a ha
    have hne : a ≠ m := by intro he; subst a; exact hma ha
    omega)
  omega

/-- An upper-only first exact block at the second upper opening is forced. -/
theorem first_block_forced (m k : ℕ) (hm : 6 ≤ m)
    (A : Finset ℕ)
    (hsub : A ⊆ (support m k).erase (m+4))
    (hs : A.sum id = m+4)
    (hu : UpperOnly ((support m k).erase (m+4)) A m) :
    A = {4,m} := by
  have hmin : ∀ x ∈ A, 2 ≤ x := by
    intro x hx
    have hxS := (Finset.mem_erase.mp (hsub hx)).2
    simp only [support, Finset.mem_union, Finset.mem_Icc] at hxS
    omega
  have hbound : ∀ x ∈ A, x ≤ m := by
    intro x hx
    have hxe := Finset.mem_erase.mp (hsub hx)
    have hxS := hxe.2
    simp only [support, Finset.mem_union, Finset.mem_Icc] at hxS
    rcases hxS with hxS | hxS
    · exact hxS.2
    have hle : x ≤ A.sum id := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
    have he : x = m+3 := by omega
    have hsum := Finset.sum_erase_add A id hx
    change (A.erase x).sum id + x = A.sum id at hsum
    have hrest : (A.erase x).sum id = 1 := by omega
    exact (sum_ne_one_of_min_two (A.erase x)
      (fun z hz ↦ hmin z (Finset.mem_erase.mp hz).2) hrest).elim
  have hmS : m ∈ (support m k).erase (m+4) := by simp [support]; omega
  have hmA := upper_only_forces_max _ A m hmS hbound hu
  have hsum := Finset.sum_erase_add A id hmA
  change (A.erase m).sum id + m = A.sum id at hsum
  have hrest : (A.erase m).sum id = 4 := by omega
  have he := sum_four_unique (A.erase m)
    (fun z hz ↦ hmin z (Finset.mem_erase.mp hz).2) hrest
  ext x
  have heMem := Finset.ext_iff.mp he x
  simp only [Finset.mem_erase, Finset.mem_singleton] at heMem
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    by_cases hxm : x = m
    · exact Or.inr hxm
    · exact Or.inl (heMem.mp ⟨hxm,hx⟩)
  · rintro (rfl | rfl)
    · exact (heMem.mpr rfl).2
    · exact hmA

/-- The residual on the structurally allowed branch after the forced first block. -/
def secondSupport (m k : ℕ) : Finset ℕ :=
  (support m k \ {m+4,4,m}).erase (m+3)

/-- No upper-only exact block is available at the next permitted upper opening. -/
theorem no_second_upper_only_block (m k : ℕ) (hm : 6 ≤ m) :
    ¬ ∃ B : Finset ℕ, B ⊆ secondSupport m k ∧
      B.sum id = m+3 ∧ UpperOnly (secondSupport m k) B m := by
  rintro ⟨B,hsub,hs,hu⟩
  have hmin : ∀ x ∈ B, 2 ≤ x := by
    intro x hx
    have hxS := (Finset.mem_sdiff.mp (Finset.mem_erase.mp (hsub hx)).2).1
    simp only [support, Finset.mem_union, Finset.mem_Icc] at hxS
    omega
  have hbound : ∀ x ∈ B, x ≤ m-1 := by
    intro x hx
    have hxS := hsub hx
    simp only [secondSupport, Finset.mem_erase, Finset.mem_sdiff,
      support, Finset.mem_union, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton] at hxS
    have hle : x ≤ B.sum id := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
    omega
  have hmS : m-1 ∈ secondSupport m k := by
    simp only [secondSupport, Finset.mem_erase, Finset.mem_sdiff,
      support, Finset.mem_union, Finset.mem_Icc,
      Finset.mem_insert, Finset.mem_singleton]
    omega
  have hupper : UpperOnly (secondSupport m k) B (m-1) := by
    intro w hw ha
    have := hu w hw ha
    omega
  have hmB := upper_only_forces_max _ B (m-1) hmS hbound hupper
  have hsum := Finset.sum_erase_add B id hmB
  change (B.erase (m-1)).sum id + (m-1) = B.sum id at hsum
  have hrest : (B.erase (m-1)).sum id = 4 := by omega
  have he := sum_four_unique (B.erase (m-1))
    (fun z hz ↦ hmin z (Finset.mem_erase.mp hz).2) hrest
  have hfour : 4 ∈ B.erase (m-1) := by rw [he]; simp
  have hfourS := hsub (Finset.mem_erase.mp hfour).2
  simp [secondSupport] at hfourS

/-- The opening and forced next witness both belong to the stated two-hole support. -/
theorem forced_branch_available (m k : ℕ) (hm : 6 ≤ m) (hk : 2 ≤ k) :
    m+4 ∈ support m k ∧
    m+3 ∈ ((support m k).erase (m+4)) \ {4,m} ∧
    (∀ x ∈ ({4,m} : Finset ℕ), x < m+3) := by
  refine ⟨?_,?_,?_⟩
  · simp only [support, Finset.mem_union, Finset.mem_Icc]
    omega
  · simp only [support, Finset.mem_union, Finset.mem_Icc, Finset.mem_sdiff,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    omega
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega


/-- A two-level exact-sum argument cannot keep every permitted witness upper. -/
theorem no_two_upper_only_steps (m k : ℕ) (hm : 6 ≤ m) (hk : 2 ≤ k) :
    let S := (support m k).erase (m+4)
    ¬ ∃ A : Finset ℕ, A ⊆ S ∧ A.sum id = m+4 ∧ UpperOnly S A m ∧
      ∀ w ∈ S \ A, (∀ a ∈ A, a < w) →
        ∃ B : Finset ℕ, B ⊆ (S \ A).erase w ∧ B.sum id = w ∧
          UpperOnly ((S \ A).erase w) B m := by
  dsimp only
  rintro ⟨A,hsub,hs,hu,hnext⟩
  have hA := first_block_forced m k hm A hsub hs hu
  subst A
  obtain ⟨_,hw,hbound⟩ := forced_branch_available m k hm hk
  have hstep := hnext (m+3) hw hbound
  have he : (((support m k).erase (m+4)) \ {4,m}).erase (m+3) =
      secondSupport m k := by
    ext x
    simp only [secondSupport, Finset.mem_erase, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [he] at hstep
  exact no_second_upper_only_block m k hm hstep

end CatchUp.UniformExactSumDescent
