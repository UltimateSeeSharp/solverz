/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/CanonicalFiveLeaves.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.CanonicalFour

/-!
# CanonicalFiveLeaves

Shared finite leaves supporting the canonical five-pair restrictions.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.CanonicalFive

open CatchUp.DeficitTwo (nonloss_of_catch)
open CatchUp.DeficitTwo (nonloss_of_continue)
open CatchUp.CanonicalSmall (nonloss_iff_check)
open CatchUp.CanonicalSmall (nonwin_iff_check)

/-- Shared eight-counter leaves for the bounded part of the sparse repair.
The unbounded tail is proved by explicit continued picks in CanonicalFive. -/
theorem sparse_bounded_leaf (q : ℕ) (hq : 12 ≤ q ∧ q ≤ 38)
    (hqe : q%2=0) (hne : q≠20) :
    Position.value ⟨{7,10,11,20,21,40,41,q+1},q-9⟩ ≠ .loss := by
  have hcases : q=12 ∨ q=14 ∨ q=16 ∨ q=18 ∨ q=22 ∨ q=24 ∨
      q=26 ∨ q=28 ∨ q=30 ∨ q=32 ∨ q=34 ∨ q=36 ∨ q=38 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply nonloss_of_catch _ _ 10 (by decide +kernel) (by omega)
    have he : ({7,10,11,20,21,40,41,12+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,13} := by decide +kernel
    rw [he,nonwin_iff_check]
    decide +kernel
  · apply nonloss_of_catch _ _ 10 (by decide +kernel) (by omega)
    have he : ({7,10,11,20,21,40,41,14+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,15} := by decide +kernel
    rw [he,nonwin_iff_check]
    decide +kernel
  · apply nonloss_of_catch _ _ 10 (by decide +kernel) (by omega)
    have he : ({7,10,11,20,21,40,41,16+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,17} := by decide +kernel
    rw [he,nonwin_iff_check]
    decide +kernel
  · apply nonloss_of_catch _ _ 10 (by decide +kernel) (by omega)
    have he : ({7,10,11,20,21,40,41,18+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,19} := by decide +kernel
    rw [he,nonwin_iff_check]
    decide +kernel
  · apply nonloss_of_catch _ _ 20 (by decide +kernel) (by omega)
    have he : ({7,10,11,20,21,40,41,22+1} : Finset ℕ).erase 20 = {7,10,11,21,40,41,23} := by decide +kernel
    rw [he,nonwin_iff_check]
    decide +kernel
  · apply nonloss_of_continue _ _ 10 (by decide +kernel) (by omega) (by decide +kernel)
    have he : ({7,10,11,20,21,40,41,24+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,25} := by decide +kernel
    rw [he,nonloss_iff_check]
    decide +kernel
  · apply nonloss_of_continue _ _ 10 (by decide +kernel) (by omega) (by decide +kernel)
    have he : ({7,10,11,20,21,40,41,26+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,27} := by decide +kernel
    rw [he,nonloss_iff_check]
    decide +kernel
  · apply nonloss_of_continue _ _ 10 (by decide +kernel) (by omega) (by decide +kernel)
    have he : ({7,10,11,20,21,40,41,28+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,29} := by decide +kernel
    rw [he,nonloss_iff_check]
    decide +kernel
  · apply nonloss_of_continue _ _ 10 (by decide +kernel) (by omega) (by decide +kernel)
    have he : ({7,10,11,20,21,40,41,30+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,31} := by decide +kernel
    rw [he,nonloss_iff_check]
    decide +kernel
  · apply nonloss_of_continue _ _ 10 (by decide +kernel) (by omega) (by decide +kernel)
    have he : ({7,10,11,20,21,40,41,32+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,33} := by decide +kernel
    rw [he,nonloss_iff_check]
    decide +kernel
  · apply nonloss_of_continue _ _ 10 (by decide +kernel) (by omega) (by decide +kernel)
    have he : ({7,10,11,20,21,40,41,34+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,35} := by decide +kernel
    rw [he,nonloss_iff_check]
    decide +kernel
  · apply nonloss_of_continue _ _ 10 (by decide +kernel) (by omega) (by decide +kernel)
    have he : ({7,10,11,20,21,40,41,36+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,37} := by decide +kernel
    rw [he,nonloss_iff_check]
    decide +kernel
  · apply nonloss_of_continue _ _ 10 (by decide +kernel) (by omega) (by decide +kernel)
    have he : ({7,10,11,20,21,40,41,38+1} : Finset ℕ).erase 10 = {7,11,20,21,40,41,39} := by decide +kernel
    rw [he,nonloss_iff_check]
    decide +kernel

/-- The missing pair at eight has a catching response by six. -/
theorem sparse_eight_repair :
    Position.value ⟨{6,7,10,11,20,21,40,41,9},8-3⟩ ≠ .loss := by
  apply nonloss_of_catch _ _ 6 (by decide +kernel) (by omega)
  have he : ({6,7,10,11,20,21,40,41,9} : Finset ℕ).erase 6 =
      {7,10,11,20,21,40,41,9} := by decide +kernel
  rw [he,nonwin_iff_check]
  decide +kernel

/-- The anchor-four boundary repair takes twenty, rather than the losing mate five. -/
theorem anchor_four_repair :
    Position.value ⟨{5,6,7,10,11,20,21,40,41},1⟩ ≠ .loss := by
  apply nonloss_of_catch _ _ 20 (by decide +kernel) (by omega)
  have he : ({5,6,7,10,11,20,21,40,41} : Finset ℕ).erase 20 =
      {5,6,7,10,11,21,40,41} := by decide +kernel
  rw [he,nonwin_iff_check]
  decide +kernel

end CatchUp.CanonicalFive
