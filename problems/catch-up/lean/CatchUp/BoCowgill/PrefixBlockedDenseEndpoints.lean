/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/PrefixBlockedDenseEndpoints.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DenseLossInjection

/-!
# Canonical shapes of the dense prefix-blocked endpoints

This module proves finite-set rigidity and a parity obstruction for the prefix-blocked alternatives
in the dense-loss injection theorem.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- A strict upper residual witness produced by an exact block in a losing dense position. -/
def DenseUpperResidualWitness (N d : ℕ) (remaining : Finset ℕ) : Prop :=
  ∃ block, ∃ hblock : block.Nonempty, ∃ w,
    block.card ≤ 2 ∧ block ⊆ remaining ∧ block.sum (fun x => x) = d ∧
      w ∈ remaining \ block ∧ (afterOpening (remaining \ block) w).value = .loss ∧
        block.max' hblock < w ∧ d < w ∧ w ≤ N

private theorem exact_three_holes
    (N a b c : ℕ) (remaining : Finset ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haI : a ∈ Finset.Icc 1 N) (hbI : b ∈ Finset.Icc 1 N)
    (hcI : c ∈ Finset.Icc 1 N)
    (ha : a ∉ remaining) (hb : b ∉ remaining) (hc : c ∉ remaining)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3) :
    (Finset.Icc 1 N) \ remaining = {a, b, c} := by
  let holes := (Finset.Icc 1 N) \ remaining
  have hbase : ({a, b, c} : Finset ℕ) ⊆ holes := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_sdiff.mpr ⟨haI, ha⟩
    · exact Finset.mem_sdiff.mpr ⟨hbI, hb⟩
    · exact Finset.mem_sdiff.mpr ⟨hcI, hc⟩
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hxbase
    have hins : insert x ({a, b, c} : Finset ℕ) ⊆ holes := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hbase hy
    have hcard := Finset.card_le_card hins
    have hfour : (insert x ({a, b, c} : Finset ℕ)).card = 4 := by
      simp only [Finset.card_insert_of_notMem hxbase]
      simp [hab, hac, hbc]
    rw [hfour] at hcard
    change holes.card ≤ 3 at hholes
    omega
  · exact hbase

/-- The deficit-two prefix endpoint is completely rigid: there are no unrecorded holes. -/
theorem second_prefix_blocked_child_shape
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hsub : remaining ⊆ Finset.Icc 1 N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3)
    (hdMissing : d ∉ remaining) (hOne : 1 ∉ remaining) (hTwo : 2 ∉ remaining) :
    remaining.erase (d - 2) =
      (((Finset.Icc 3 N).erase (d - 2)).erase d) := by
  have hshape := exact_three_holes N 1 2 d remaining (by omega) (by omega) (by omega)
    (by simp; omega) (by simp; omega) (by simp; omega)
    hOne hTwo hdMissing hholes
  ext x
  simp only [Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨hxdTwo, hxR⟩
    have hxI := Finset.mem_Icc.mp (hsub hxR)
    have hxNeD : x ≠ d := by
      intro hxd
      apply hdMissing
      simpa [hxd] using hxR
    have hxNeOne : x ≠ 1 := by
      intro hxOne
      apply hOne
      simpa [hxOne] using hxR
    have hxNeTwo : x ≠ 2 := by
      intro hxTwo
      apply hTwo
      simpa [hxTwo] using hxR
    exact ⟨hxNeD, hxdTwo, by omega, hxI.2⟩
  · rintro ⟨hxd, hxdTwo, hxThree, hxN⟩
    refine ⟨hxdTwo, ?_⟩
    by_contra hxR
    have hxHole : x ∈ (Finset.Icc 1 N) \ remaining :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hxN⟩, hxR⟩
    rw [hshape] at hxHole
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxHole
    rcases hxHole with rfl | rfl | rfl <;> omega

/-- Under an even interval total, the deficit-two prefix alternative has odd effective total. -/
theorem second_prefix_blocked_effective_total_not_even
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hsub : remaining ⊆ Finset.Icc 1 N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3)
    (hdMissing : d ∉ remaining) (hOne : 1 ∉ remaining) (hTwo : 2 ∉ remaining)
    (hintervalEven : Even ((Finset.Icc 1 N).sum (fun x => x))) :
    ¬ Even (d + remaining.sum (fun x => x)) := by
  intro heffectiveEven
  have hshape := exact_three_holes N 1 2 d remaining (by omega) (by omega) (by omega)
    (by simp; omega) (by simp; omega) (by simp; omega)
    hOne hTwo hdMissing hholes
  have hsum := Finset.sum_sdiff (f := fun x : ℕ => x) hsub
  rw [hshape] at hsum
  have hholesSum : ({1, 2, d} : Finset ℕ).sum (fun x => x) = d + 3 := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega)]
    simp
    omega
  rw [hholesSum] at hsum
  rcases hintervalEven with ⟨intervalHalf, hintervalHalf⟩
  rcases heffectiveEven with ⟨effectiveHalf, heffectiveHalf⟩
  omega

/-- In the first deficit-one prefix alternative, even interval and effective totals force a
genuine third parent hole. That hole is odd, and the child has exactly the corresponding four
holes. -/
theorem first_prefix_blocked_exists_odd_hole_and_child_shape
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hsub : remaining ⊆ Finset.Icc 1 N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3)
    (hdMissing : d ∉ remaining) (hOne : 1 ∉ remaining)
    (hPred : d - 1 ∈ remaining)
    (hintervalEven : Even ((Finset.Icc 1 N).sum (fun x => x)))
    (heffectiveEven : Even (d + remaining.sum (fun x => x))) :
    ∃ h, h ∈ Finset.Icc 1 N ∧ h ∉ remaining ∧ h ≠ 1 ∧ h ≠ d ∧ Odd h ∧
      remaining.erase (d - 1) =
        ((((Finset.Icc 2 N).erase (d - 1)).erase d).erase h) := by
  let holes := (Finset.Icc 1 N) \ remaining
  have hOneHole : 1 ∈ holes := by
    exact Finset.mem_sdiff.mpr ⟨by simp; omega, hOne⟩
  have hdHole : d ∈ holes := by
    exact Finset.mem_sdiff.mpr ⟨by simp; omega, hdMissing⟩
  have hextra : ∃ h ∈ holes, h ≠ 1 ∧ h ≠ d := by
    by_contra hno
    have hsubset : holes ⊆ ({1, d} : Finset ℕ) := by
      intro x hx
      by_cases hxOne : x = 1
      · simp [hxOne]
      by_cases hxD : x = d
      · simp [hxD]
      exact (hno ⟨x, hx, hxOne, hxD⟩).elim
    have hpairSubset : ({1, d} : Finset ℕ) ⊆ holes := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hOneHole
      · exact hdHole
    have hshapeTwo : holes = {1, d} :=
      Finset.Subset.antisymm hsubset hpairSubset
    have hsum := Finset.sum_sdiff (f := fun x : ℕ => x) hsub
    change holes.sum (fun x => x) + remaining.sum (fun x => x) =
      (Finset.Icc 1 N).sum (fun x => x) at hsum
    rw [hshapeTwo] at hsum
    have hholesSum : ({1, d} : Finset ℕ).sum (fun x => x) = d + 1 := by
      rw [Finset.sum_pair (by omega)]
      omega
    rw [hholesSum] at hsum
    rcases hintervalEven with ⟨intervalHalf, hintervalHalf⟩
    rcases heffectiveEven with ⟨effectiveHalf, heffectiveHalf⟩
    omega
  obtain ⟨h, hhHole, hhOne, hhD⟩ := hextra
  have hhI : h ∈ Finset.Icc 1 N := (Finset.mem_sdiff.mp hhHole).1
  have hhMissing : h ∉ remaining := (Finset.mem_sdiff.mp hhHole).2
  have hshape := exact_three_holes N 1 d h remaining
    (by omega) (Ne.symm hhOne) (Ne.symm hhD)
    (by simp; omega) (by simp; omega) hhI
    hOne hdMissing hhMissing hholes
  have hhOdd : Odd h := by
    apply Nat.not_even_iff_odd.mp
    intro hhEven
    have hsum := Finset.sum_sdiff (f := fun x : ℕ => x) hsub
    rw [hshape] at hsum
    have hholesSum : ({1, d, h} : Finset ℕ).sum (fun x => x) = d + h + 1 := by
      rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega)]
      simp
      omega
    rw [hholesSum] at hsum
    rcases hintervalEven with ⟨intervalHalf, hintervalHalf⟩
    rcases heffectiveEven with ⟨effectiveHalf, heffectiveHalf⟩
    rcases hhEven with ⟨holeHalf, hholeHalf⟩
    omega
  refine ⟨h, hhI, hhMissing, hhOne, hhD, hhOdd, ?_⟩
  ext x
  simp only [Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨hxdPred, hxR⟩
    have hxI := Finset.mem_Icc.mp (hsub hxR)
    have hxNeD : x ≠ d := by
      intro hxd
      apply hdMissing
      simpa [hxd] using hxR
    have hxNeH : x ≠ h := by
      intro hxh
      apply hhMissing
      simpa [hxh] using hxR
    have hxNeOne : x ≠ 1 := by
      intro hxOne
      apply hOne
      simpa [hxOne] using hxR
    exact ⟨hxNeH, hxNeD, hxdPred, by omega, hxI.2⟩
  · rintro ⟨hxNeH, hxNeD, hxdPred, hxTwo, hxN⟩
    refine ⟨hxdPred, ?_⟩
    by_contra hxR
    have hxHole : x ∈ (Finset.Icc 1 N) \ remaining :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hxN⟩, hxR⟩
    rw [hshape] at hxHole
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxHole
    rcases hxHole with rfl | rfl | rfl <;> omega

/-- The deficit-one third endpoint is the interval tail with one consecutive triple removed. -/
theorem third_prefix_blocked_child_shape
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hsub : remaining ⊆ Finset.Icc 1 N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3)
    (hdMissing : d ∉ remaining) (hTwo : 2 ∉ remaining)
    (hPred : d - 1 ∉ remaining) :
    (remaining.erase (d - 2)).erase 1 =
      ((((Finset.Icc 3 N).erase (d - 2)).erase (d - 1)).erase d) := by
  have hshape := exact_three_holes N 2 (d - 1) d remaining
    (by omega) (by omega) (by omega)
    (by simp; omega) (by simp; omega) (by simp; omega)
    hTwo hPred hdMissing hholes
  ext x
  simp only [Finset.mem_erase, Finset.mem_Icc]
  constructor
  · rintro ⟨hxOne, hxdTwo, hxR⟩
    have hxI := Finset.mem_Icc.mp (hsub hxR)
    have hxNeD : x ≠ d := by
      intro hxd
      apply hdMissing
      simpa [hxd] using hxR
    have hxNePred : x ≠ d - 1 := by
      intro hxd
      apply hPred
      simpa [hxd] using hxR
    have hxNeTwo : x ≠ 2 := by
      intro hxTwo
      apply hTwo
      simpa [hxTwo] using hxR
    exact ⟨hxNeD, hxNePred, hxdTwo, by omega, hxI.2⟩
  · rintro ⟨hxd, hxdPred, hxdTwo, hxThree, hxN⟩
    refine ⟨by omega, hxdTwo, ?_⟩
    by_contra hxR
    have hxHole : x ∈ (Finset.Icc 1 N) \ remaining :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hxN⟩, hxR⟩
    rw [hshape] at hxHole
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxHole
    rcases hxHole with rfl | rfl | rfl <;> omega

/-- If both the interval and parent effective totals are even in the third prefix alternative, the
deficit is odd. -/
theorem third_prefix_blocked_deficit_odd
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hsub : remaining ⊆ Finset.Icc 1 N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3)
    (hdMissing : d ∉ remaining) (hTwo : 2 ∉ remaining)
    (hPred : d - 1 ∉ remaining)
    (hintervalEven : Even ((Finset.Icc 1 N).sum (fun x => x)))
    (heffectiveEven : Even (d + remaining.sum (fun x => x))) :
    Odd d := by
  apply Nat.not_even_iff_odd.mp
  intro hdEven
  have hshape := exact_three_holes N 2 (d - 1) d remaining
    (by omega) (by omega) (by omega)
    (by simp; omega) (by simp; omega) (by simp; omega)
    hTwo hPred hdMissing hholes
  have hsum := Finset.sum_sdiff (f := fun x : ℕ => x) hsub
  rw [hshape] at hsum
  have hholesSum : ({2, d - 1, d} : Finset ℕ).sum (fun x => x) = 2 * d + 1 := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega)]
    simp
    omega
  rw [hholesSum] at hsum
  rcases hintervalEven with ⟨intervalHalf, hintervalHalf⟩
  rcases heffectiveEven with ⟨effectiveHalf, heffectiveHalf⟩
  rcases hdEven with ⟨deficitHalf, hdeficitHalf⟩
  omega

/-- A hypothetical even dense loss either has a strict upper exact-block witness or descends to
one of two explicit odd-parameter deficit-one endpoint families. -/
theorem even_dense_loss_forces_upper_or_odd_prefix_endpoint
    (N d : ℕ) (remaining : Finset ℕ)
    (hd : 7 ≤ d) (hdN : d ≤ N)
    (hsub : remaining ⊆ Finset.Icc 1 N)
    (hholes : ((Finset.Icc 1 N) \ remaining).card ≤ 3)
    (hintervalEven : Even ((Finset.Icc 1 N).sum (fun x => x)))
    (heffectiveEven : Even (d + remaining.sum (fun x => x)))
    (hloss : (⟨remaining, d⟩ : Position).value = .loss) :
    DenseUpperResidualWitness N d remaining ∨
      (∃ h, h ∈ Finset.Icc 1 N ∧ h ∉ remaining ∧ h ≠ 1 ∧ h ≠ d ∧ Odd h ∧
        (⟨(((Finset.Icc 2 N).erase (d - 1)).erase d).erase h, 1⟩ : Position).value = .loss) ∨
      (Odd d ∧
        (⟨(((Finset.Icc 3 N).erase (d - 2)).erase (d - 1)).erase d, 1⟩ : Position).value =
          .loss) := by
  rcases dense_loss_forces_upper_residual_or_small_prefix_blocked_loss
      N d remaining hd hdN hsub hholes hloss with
    hupper | hfirst | hsecond | hthird
  · exact Or.inl hupper
  · right
    left
    rcases hfirst with ⟨hdMissing, hOne, hPred, hchildLoss⟩
    obtain ⟨h, hhI, hhMissing, hhOne, hhD, hhOdd, hshape⟩ :=
      first_prefix_blocked_exists_odd_hole_and_child_shape
        N d remaining hd hdN hsub hholes hdMissing hOne hPred hintervalEven heffectiveEven
    refine ⟨h, hhI, hhMissing, hhOne, hhD, hhOdd, ?_⟩
    rw [← hshape]
    exact hchildLoss
  · exact (second_prefix_blocked_effective_total_not_even
      N d remaining hd hdN hsub hholes hsecond.1 hsecond.2.1 hsecond.2.2.1
      hintervalEven heffectiveEven).elim
  · right
    right
    rcases hthird with
      ⟨hdMissing, _hOne, hTwo, hPred, _hNear, hchildLoss⟩
    have hshape := third_prefix_blocked_child_shape
      N d remaining hd hdN hsub hholes hdMissing hTwo hPred
    have hdOdd := third_prefix_blocked_deficit_odd
      N d remaining hd hdN hsub hholes hdMissing hTwo hPred hintervalEven heffectiveEven
    refine ⟨hdOdd, ?_⟩
    rw [← hshape]
    exact hchildLoss

end CatchUp
