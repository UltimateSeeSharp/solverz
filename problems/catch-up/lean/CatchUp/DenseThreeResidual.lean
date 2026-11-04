/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseThreeResidual.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.DenseTwoResidual
public import CatchUp.DenseGapMass

/-! # Closing the dense maximal-block gap branch with three residual counters -/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseThreeResidual

open CatchUp (Position.move_outcome_eq_loss_of_value_eq_loss)

/-- The six small arithmetic parameters used by the finite classifier. -/
structure Seed where
  b : ℕ
  tail : Finset ℕ
  w : ℕ
  u : ℕ
  v : ℕ
  z : ℕ
  deriving DecidableEq

def Seed.block (q : Seed) : Finset ℕ := insert q.b q.tail

def Seed.residual (q : Seed) : Position := ⟨{q.u, q.v, q.z}, q.w⟩

def Seed.successor (q : Seed) : Position :=
  ⟨q.block ∪ {q.u, q.v, q.z}, q.b + q.tail.sum (fun x ↦ x) - q.w⟩

/-- The possible block tails after the gap-refined mass bound. -/
def tails : Finset (Finset ℕ) :=
  {∅, {1}, {2}, {3}, {4}, {5}, {1, 2}, {1, 3}, {1, 4}, {1, 5}, {2, 3}, {2, 4}}

/-- Every positive tail with at most two counters and the required mass is listed. -/
theorem tail_classification :
    ∀ A ∈ (Icc 1 6).powerset, A.card ≤ 2 → A.sum (fun x ↦ x) ≤ A.card + 4 →
      A ∈ tails := by decide +kernel

/-- All static arithmetic cases; the exhaustive classifier below proves completeness. -/
def staticSeeds : ℕ → Finset Seed
  | 9 => {⟨5, {2}, 6, 3, 4, 9⟩,
      ⟨5, {2}, 6, 3, 8, 9⟩,
      ⟨4, {3}, 5, 6, 8, 9⟩,
      ⟨4, {3}, 6, 5, 8, 9⟩,
      ⟨5, {3}, 6, 1, 4, 9⟩,
      ⟨5, {3}, 7, 2, 4, 9⟩,
      ⟨6, {2}, 7, 3, 5, 9⟩,
      ⟨5, {3}, 6, 4, 7, 9⟩,
      ⟨5, {3}, 7, 4, 6, 9⟩,
      ⟨7, {2}, 8, 3, 4, 5⟩,
      ⟨7, {2}, 8, 3, 5, 6⟩,
      ⟨6, {3}, 7, 4, 5, 8⟩,
      ⟨6, {3}, 8, 4, 5, 7⟩}
  | 10 => {⟨7, {2}, 8, 3, 4, 5⟩,
      ⟨7, {2}, 8, 3, 5, 6⟩,
      ⟨6, {3}, 7, 4, 5, 8⟩,
      ⟨6, {3}, 8, 4, 5, 7⟩,
      ⟨6, {3}, 7, 1, 4, 10⟩,
      ⟨5, {4}, 6, 1, 7, 10⟩,
      ⟨5, {4}, 7, 1, 6, 10⟩,
      ⟨6, {3}, 7, 4, 5, 10⟩,
      ⟨6, {3}, 8, 2, 4, 10⟩,
      ⟨5, {4}, 6, 2, 8, 10⟩,
      ⟨5, {4}, 8, 2, 6, 10⟩,
      ⟨7, {2}, 8, 3, 5, 10⟩,
      ⟨5, {4}, 7, 3, 8, 10⟩,
      ⟨5, {4}, 8, 3, 7, 10⟩,
      ⟨7, {2}, 8, 4, 6, 10⟩,
      ⟨6, {3}, 7, 5, 8, 10⟩,
      ⟨6, {3}, 8, 5, 7, 10⟩,
      ⟨7, {3}, 8, 1, 4, 5⟩,
      ⟨7, {3}, 8, 1, 5, 6⟩,
      ⟨7, {3}, 9, 2, 4, 5⟩,
      ⟨7, {3}, 9, 2, 5, 6⟩,
      ⟨7, {3}, 9, 4, 5, 6⟩,
      ⟨8, {2}, 9, 3, 4, 6⟩,
      ⟨8, {2}, 9, 4, 5, 6⟩,
      ⟨8, {2}, 9, 3, 5, 7⟩,
      ⟨7, {3}, 8, 4, 5, 9⟩,
      ⟨7, {3}, 9, 4, 5, 8⟩,
      ⟨8, {2}, 9, 4, 6, 7⟩,
      ⟨7, {3}, 8, 5, 6, 9⟩,
      ⟨7, {3}, 9, 5, 6, 8⟩}
  | 11 => {⟨5, {1, 3}, 7, 4, 10, 11⟩,
      ⟨6, {1, 3}, 8, 4, 5, 11⟩,
      ⟨7, {1, 3}, 9, 4, 5, 6⟩,
      ⟨7, {4}, 8, 1, 5, 6⟩,
      ⟨7, {4}, 9, 1, 3, 5⟩,
      ⟨8, {3}, 9, 1, 4, 6⟩,
      ⟨6, {5}, 8, 1, 4, 9⟩,
      ⟨6, {5}, 9, 1, 4, 8⟩,
      ⟨8, {3}, 9, 4, 5, 6⟩,
      ⟨8, {3}, 9, 1, 5, 7⟩,
      ⟨7, {4}, 8, 1, 6, 9⟩,
      ⟨7, {4}, 9, 1, 6, 8⟩,
      ⟨8, {3}, 9, 4, 6, 7⟩,
      ⟨7, {4}, 8, 5, 6, 9⟩,
      ⟨7, {4}, 9, 5, 6, 8⟩,
      ⟨7, {4}, 10, 2, 3, 5⟩,
      ⟨6, {5}, 7, 2, 3, 10⟩,
      ⟨6, {5}, 10, 2, 3, 7⟩,
      ⟨7, {4}, 10, 3, 5, 6⟩,
      ⟨8, {3}, 10, 2, 4, 6⟩,
      ⟨6, {5}, 8, 2, 4, 10⟩,
      ⟨6, {5}, 10, 2, 4, 8⟩,
      ⟨8, {3}, 10, 2, 5, 7⟩,
      ⟨8, {3}, 10, 4, 5, 7⟩,
      ⟨7, {4}, 8, 2, 6, 10⟩,
      ⟨7, {4}, 10, 2, 6, 8⟩,
      ⟨8, {3}, 10, 5, 6, 7⟩,
      ⟨9, {2}, 10, 3, 4, 5⟩,
      ⟨9, {2}, 10, 3, 5, 6⟩,
      ⟨6, {5}, 9, 3, 4, 10⟩,
      ⟨6, {5}, 10, 3, 4, 9⟩,
      ⟨9, {2}, 10, 3, 4, 7⟩,
      ⟨9, {2}, 10, 4, 5, 7⟩,
      ⟨9, {2}, 10, 3, 6, 7⟩,
      ⟨7, {4}, 9, 3, 6, 10⟩,
      ⟨7, {4}, 10, 3, 6, 9⟩,
      ⟨9, {2}, 10, 5, 6, 7⟩,
      ⟨7, {4}, 9, 5, 6, 10⟩,
      ⟨7, {4}, 10, 5, 6, 9⟩,
      ⟨9, {2}, 10, 3, 5, 8⟩,
      ⟨8, {3}, 9, 4, 5, 10⟩,
      ⟨8, {3}, 10, 4, 5, 9⟩,
      ⟨9, {2}, 10, 4, 6, 8⟩,
      ⟨8, {3}, 9, 5, 6, 10⟩,
      ⟨8, {3}, 10, 5, 6, 9⟩,
      ⟨9, {2}, 10, 3, 7, 8⟩,
      ⟨8, {3}, 9, 4, 7, 10⟩,
      ⟨8, {3}, 10, 4, 7, 9⟩,
      ⟨9, {2}, 10, 5, 7, 8⟩,
      ⟨7, {4}, 8, 5, 9, 10⟩,
      ⟨7, {4}, 9, 5, 8, 10⟩,
      ⟨7, {4}, 10, 5, 8, 9⟩,
      ⟨8, {3}, 9, 6, 7, 10⟩,
      ⟨8, {3}, 10, 6, 7, 9⟩,
      ⟨6, {5}, 7, 8, 9, 10⟩,
      ⟨6, {5}, 8, 7, 9, 10⟩,
      ⟨6, {5}, 9, 7, 8, 10⟩,
      ⟨6, {5}, 10, 7, 8, 9⟩}
  | 12 => {⟨7, {1, 3}, 9, 4, 5, 6⟩,
      ⟨7, {1, 3}, 9, 4, 5, 12⟩,
      ⟨7, {1, 3}, 9, 5, 6, 12⟩,
      ⟨6, {1, 4}, 8, 5, 9, 12⟩,
      ⟨6, {1, 4}, 9, 5, 8, 12⟩,
      ⟨6, {2, 3}, 7, 5, 10, 12⟩,
      ⟨6, {2, 3}, 10, 5, 7, 12⟩,
      ⟨7, {1, 4}, 10, 3, 5, 6⟩,
      ⟨8, {1, 3}, 10, 4, 5, 7⟩,
      ⟨8, {1, 3}, 10, 5, 6, 7⟩,
      ⟨7, {1, 4}, 9, 5, 6, 10⟩,
      ⟨7, {1, 4}, 10, 5, 6, 9⟩,
      ⟨7, {2, 3}, 11, 4, 5, 6⟩,
      ⟨7, {2, 3}, 8, 5, 6, 11⟩,
      ⟨7, {2, 3}, 11, 5, 6, 8⟩}
  | 13 => {⟨8, {1, 4}, 10, 5, 6, 7⟩,
      ⟨7, {1, 5}, 11, 3, 4, 6⟩,
      ⟨8, {1, 4}, 11, 3, 5, 7⟩,
      ⟨9, {1, 3}, 11, 4, 5, 6⟩,
      ⟨9, {1, 3}, 11, 4, 6, 7⟩,
      ⟨9, {1, 3}, 11, 4, 5, 8⟩,
      ⟨9, {1, 3}, 11, 5, 6, 8⟩,
      ⟨9, {1, 3}, 11, 4, 7, 8⟩,
      ⟨9, {1, 3}, 11, 6, 7, 8⟩,
      ⟨8, {1, 4}, 10, 5, 6, 11⟩,
      ⟨8, {1, 4}, 11, 5, 6, 10⟩,
      ⟨8, {1, 4}, 10, 6, 7, 11⟩,
      ⟨8, {1, 4}, 11, 6, 7, 10⟩,
      ⟨7, {1, 5}, 9, 6, 10, 11⟩,
      ⟨7, {1, 5}, 10, 6, 9, 11⟩,
      ⟨7, {1, 5}, 11, 6, 9, 10⟩,
      ⟨7, {2, 4}, 12, 3, 5, 6⟩,
      ⟨8, {2, 3}, 12, 4, 5, 7⟩,
      ⟨8, {2, 3}, 12, 5, 6, 7⟩,
      ⟨8, {2, 3}, 9, 5, 6, 12⟩,
      ⟨8, {2, 3}, 12, 5, 6, 9⟩,
      ⟨8, {2, 3}, 9, 6, 7, 12⟩,
      ⟨8, {2, 3}, 12, 6, 7, 9⟩,
      ⟨7, {2, 4}, 8, 6, 10, 12⟩,
      ⟨7, {2, 4}, 10, 6, 8, 12⟩,
      ⟨7, {2, 4}, 12, 6, 8, 10⟩}
  | _ => ∅

/-- Cases surviving the actual residual-loss guard, certified below. -/
def liveSeeds : Finset Seed :=
  {⟨5, {2}, 6, 3, 8, 9⟩,
   ⟨5, {4}, 6, 1, 7, 10⟩,
   ⟨5, {4}, 6, 2, 8, 10⟩,
   ⟨5, {4}, 7, 3, 8, 10⟩,
   ⟨7, {3}, 9, 4, 5, 6⟩,
   ⟨8, {2}, 9, 4, 5, 6⟩,
   ⟨5, {1, 3}, 7, 4, 10, 11⟩,
   ⟨7, {1, 3}, 9, 4, 5, 6⟩,
   ⟨8, {3}, 9, 4, 5, 6⟩,
   ⟨8, {3}, 10, 5, 6, 7⟩,
   ⟨9, {2}, 10, 5, 6, 7⟩,
   ⟨7, {4}, 8, 5, 9, 10⟩,
   ⟨8, {1, 3}, 10, 5, 6, 7⟩,
   ⟨7, {2, 3}, 11, 5, 6, 8⟩,
   ⟨8, {1, 4}, 10, 5, 6, 7⟩,
   ⟨9, {1, 3}, 11, 5, 6, 8⟩,
   ⟨9, {1, 3}, 11, 6, 7, 8⟩,
   ⟨7, {1, 5}, 9, 6, 10, 11⟩,
   ⟨8, {2, 3}, 12, 6, 7, 9⟩}

/-- The full arithmetic conditions on a reconstructed support, before any game-value guard. -/
def finiteConfiguration (N b w : ℕ) (A C : Finset ℕ) : Prop :=
  let B := insert b A
  let S := insert w B ∪ C
  let d := b + A.sum (fun x ↦ x)
  (∀ a ∈ A, a < b) ∧ Disjoint C (insert w B) ∧ d ≤ N ∧
    2 * (Icc 1 N \ S).card + 1 ≤ d ∧ Even (S.sum (fun x ↦ x) + d) ∧
    (∀ D ∈ S.powerset, D.sum (fun x ↦ x) = d → ∀ x ∈ D, x ≤ b) ∧
    (∀ D ∈ S.powerset, D.sum (fun x ↦ x) ≠ d - w) ∧ w ≤ C.sum (fun x ↦ x)

instance (N b w : ℕ) (A C : Finset ℕ) : Decidable (finiteConfiguration N b w A C) := by
  unfold finiteConfiguration
  infer_instance

/-- A bounded ambient slice; cheap cardinal arithmetic precedes the residual loop. -/
def boundedAt (N : ℕ) : Prop :=
    ∀ b ∈ Icc 1 N, ∀ A ∈ tails,
      ∀ w ∈ Icc (b + 1) (b + A.sum (fun x ↦ x) - 1),
      b + A.sum (fun x ↦ x) ≤ N →
      2 * N + 1 ≤ b + A.sum (fun x ↦ x) + 2 * (A.card + 5) →
      (∀ D ∈ A.powerset, D.sum (fun x ↦ x) ≠ b + A.sum (fun x ↦ x) - w) →
      ∀ u ∈ Icc 1 N, ∀ v ∈ Icc (u + 1) N, ∀ z ∈ Icc (v + 1) N,
        finiteConfiguration N b w A {u, v, z} →
          (⟨b, A, w, u, v, z⟩ : Seed) ∈ staticSeeds N

instance (N : ℕ) : Decidable (boundedAt N) := by
  unfold boundedAt
  infer_instance

private theorem bounded_below_ten : ∀ N ∈ range 10, boundedAt N := by decide +kernel
private theorem bounded_ten : boundedAt 10 := by decide +kernel
private theorem bounded_eleven : boundedAt 11 := by decide +kernel
private theorem bounded_twelve : boundedAt 12 := by decide +kernel
private theorem bounded_thirteen : boundedAt 13 := by decide +kernel

/-- Exhaustive pure-arithmetic classification at every supplied ambient interval size. -/
theorem bounded_classification : ∀ N ∈ range 14, boundedAt N := by
  intro N hN
  by_cases hsmall : N < 10
  · exact bounded_below_ten N (mem_range.mpr hsmall)
  · have hrange := mem_range.mp hN
    have hcases : N = 10 ∨ N = 11 ∨ N = 12 ∨ N = 13 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact bounded_ten
    · exact bounded_eleven
    · exact bounded_twelve
    · exact bounded_thirteen

/-- Kernel values of every static residual, retaining the actual loss guard. -/
theorem residual_filter : ∀ N ∈ range 14, ∀ q ∈ staticSeeds N,
    q.residual.eval = .loss → q ∈ liveSeeds := by
  decide +kernel

/-- Every live case has a safe exact-block pick that ends its turn immediately. -/
theorem live_safe_entries (q : Seed) (hq : q ∈ liveSeeds) :
    ∃ x ∈ q.block, q.successor.deficit ≤ x ∧
      (q.successor.afterPick x).eval ≠ .win := by
  simp only [liveSeeds, mem_insert, mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

private theorem ordered_triple (C : Finset ℕ) (hcard : C.card = 3) :
    ∃ u v z, u < v ∧ v < z ∧ C = {u, v, z} := by
  have hne : C.Nonempty := card_pos.mp (by omega)
  let u := C.min' hne
  have hu : u ∈ C := min'_mem C hne
  have herase : (C.erase u).card = 2 := by
    have hh := card_erase_add_one hu
    omega
  obtain ⟨x, y, hxy, hpair⟩ := card_eq_two.mp herase
  have hordered : ∃ v z, v < z ∧ C.erase u = {v, z} := by
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact ⟨x, y, hlt, hpair⟩
    · exact ⟨y, x, hgt, by simpa only [pair_comm] using hpair⟩
  obtain ⟨v, z, hvz, he⟩ := hordered
  have hv : v ∈ C.erase u := by rw [he]; simp
  have huv : u < v := by
    have hle : u ≤ v := min'_le C v (mem_of_mem_erase hv)
    have hne' := ne_of_mem_erase hv
    omega
  refine ⟨u, v, z, huv, hvz, ?_⟩
  calc
    C = insert u (C.erase u) := (insert_erase hu).symm
    _ = {u, v, z} := by rw [he]

/-- A nonterminal losing three-counter residual admits a safe first pick in the exact block.
The pick catches up immediately; the outcome uses the full minimax semantics. -/
theorem three_residual_safe_block_entry
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (heven : Even (S.sum (fun x ↦ x) + d))
    (hB : B ⊆ S) (hsumB : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hmax : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) = d → ∀ x ∈ D, x ≤ b)
    (hw : w ∈ S \ B) (hbw : b < w) (hwd : w < d)
    (hgap : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) ≠ d - w)
    (hcard : ((S \ B).erase w).card = 3)
    (hcatch : w ≤ ((S \ B).erase w).sum (fun x ↦ x))
    (hresloss : (afterOpening (S \ B) w).value = .loss) :
    ∃ x ∈ B, d - w ≤ x ∧ (⟨S.erase w, d - w⟩ : Position).moveOutcome x ≠ .loss := by
  classical
  let C := (S \ B).erase w
  let A := B.erase b
  have hCS : C ⊆ S := by
    intro x hx
    exact (mem_sdiff.mp (mem_of_mem_erase hx)).1
  obtain ⟨u, v, z, huv, hvz, heC⟩ := ordered_triple C hcard
  have huC : u ∈ C := by rw [heC]; simp
  have hvC : v ∈ C := by rw [heC]; simp
  have hzC : z ∈ C := by rw [heC]; simp
  have huN := mem_Icc.mp (hS (hCS huC))
  have hvN := mem_Icc.mp (hS (hCS hvC))
  have hzN := mem_Icc.mp (hS (hCS hzC))
  obtain ⟨D, hDS, hsumD, a, haD, ha⟩ :=
    DenseLossSubsumGap.exists_large_exact_block_member N (Icc 1 N \ S).card d S
      hS le_rfl hlarge hdN
  have hnear : d - (Icc 1 N \ S).card ≤ b := le_trans ha (hmax D hDS hsumD a haD)
  obtain ⟨hk, hNbound⟩ := DenseGapMass.small_gap_block_bound N d b w S B hS hlarge hdN
    hB hsumB hb hnear hw hbw hwd hgap (by omega)
  have hN : N ≤ 13 := by omega
  have hholes := DenseBlockMass.holes_le_block_add_residual N d w S B hS hB hw hlarge hdN
  have hpart := DenseBlockMass.residual_partition N w S B hS hB hw
  have hcardA : A.card + 1 = B.card := card_erase_add_one hb
  have hsumA : A.sum (fun x ↦ x) + b = d := by
    simpa only [hsumB] using sum_erase_add B (fun x : ℕ ↦ x) hb
  have hmassA : A.sum (fun x ↦ x) ≤ A.card + 4 := by omega
  have hsmallA : A.card ≤ 2 := by omega
  have hAa : ∀ a ∈ A, a < b := by
    intro x hx
    have hle := hmax B hB hsumB x (mem_of_mem_erase hx)
    have hne := ne_of_mem_erase hx
    omega
  have hA6 : A ⊆ Icc 1 6 := by
    intro x hx
    have hp := mem_Icc.mp (hS (hB (mem_of_mem_erase hx)))
    have hs := single_le_sum (fun x _ ↦ Nat.zero_le x) hx
    change x ≤ A.sum (fun x ↦ x) at hs
    exact mem_Icc.mpr ⟨hp.1, by omega⟩
  have htail : A ∈ tails := tail_classification A (mem_powerset.mpr hA6) hsmallA hmassA
  have heB : insert b A = B := insert_erase hb
  have hrest : S \ B = insert w C := (insert_erase hw).symm
  have heS : S = insert w B ∪ {u, v, z} := by
    calc
      S = (S \ B) ∪ B := (sdiff_union_of_subset hB).symm
      _ = insert w C ∪ B := by rw [hrest]
      _ = insert w B ∪ {u, v, z} := by
        rw [heC]
        ext x
        simp only [mem_union, mem_insert]
        tauto
  have hed : d = b + A.sum (fun x ↦ x) := by omega
  have hdis : Disjoint C (insert w B) := by
    refine disjoint_left.mpr ?_
    intro x hx hy
    have hh := mem_erase.mp hx
    rcases mem_insert.mp hy with rfl | hxB
    · exact hh.1 rfl
    · exact (mem_sdiff.mp hh.2).2 hxB
  have hconfig : finiteConfiguration N b w A {u, v, z} := by
    dsimp only [finiteConfiguration]
    rw [heB, ← heS, ← hed]
    refine ⟨hAa, ?_, hdN, hlarge, heven, ?_, ?_, ?_⟩
    · rwa [← heC]
    · intro D hD hsum x hx
      exact hmax D (mem_powerset.mp hD) hsum x hx
    · intro D hD
      exact hgap D (mem_powerset.mp hD)
    · rwa [← heC]
  have hbN := mem_Icc.mp (hS (hB hb))
  have htailgap : ∀ D ∈ A.powerset,
      D.sum (fun x ↦ x) ≠ b + A.sum (fun x ↦ x) - w := by
    intro D hD
    rw [← hed]
    exact hgap D (fun x hx ↦ hB (mem_of_mem_erase (mem_powerset.mp hD hx)))
  let q : Seed := ⟨b, A, w, u, v, z⟩
  have hq : q ∈ staticSeeds N := bounded_classification N (mem_range.mpr (by omega)) b
    (mem_Icc.mpr hbN) A htail w (mem_Icc.mpr ⟨by omega, by omega⟩)
    (by omega) (by omega) htailgap u (mem_Icc.mpr huN)
    v (mem_Icc.mpr ⟨by omega, hvN.2⟩) z (mem_Icc.mpr ⟨by omega, hzN.2⟩) hconfig
  have hqres : q.residual = afterOpening (S \ B) w := by
    change (⟨{u, v, z}, w⟩ : Position) = ⟨C, w⟩
    rw [← heC]
  have hqlive : q ∈ liveSeeds := residual_filter N (mem_range.mpr (by omega)) q hq (by
    rw [hqres, Position.eval_eq_value]
    exact hresloss)
  obtain ⟨x, hx, hxt, hsafe⟩ := live_safe_entries q hqlive
  have hqB : q.block = B := heB
  have hqP : q.successor = (⟨S.erase w, d - w⟩ : Position) := by
    have hwB : w ∉ B := (mem_sdiff.mp hw).2
    have hwC : w ∉ ({u, v, z} : Finset ℕ) := by rw [← heC]; simp [C]
    change (⟨insert b A ∪ {u, v, z}, b + A.sum (fun x ↦ x) - w⟩ : Position) =
      ⟨S.erase w, d - w⟩
    congr 1
    · change insert b A ∪ {u, v, z} = S.erase w
      rw [heB, heS]
      ext y
      by_cases hy : y = w
      · subst y
        simp only [mem_union, mem_erase, ne_eq, not_true_eq_false, false_and, iff_false]
        exact not_or.mpr ⟨hwB, hwC⟩
      · simp [hy]
    · change b + A.sum (fun x ↦ x) - w = d - w
      rw [← hed]
  rw [hqB] at hx
  rw [hqP] at hxt hsafe
  refine ⟨x, hx, hxt, ?_⟩
  simp only [Position.moveOutcome, ite_eq_right (not_lt_of_ge hxt)]
  rw [← Position.eval_eq_value]
  cases he : (Position.afterPick ⟨S.erase w, d - w⟩ x).eval <;> simp_all

/-- The full dense maximal-block gap branch has a nonlosing successor for residual size at most
three, for arbitrary legal input supports and exact blocks. -/
theorem small_residual_successor_nonloss
    (N d b w : ℕ) (S B : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hlarge : 2 * (Icc 1 N \ S).card + 1 ≤ d) (hdN : d ≤ N)
    (heven : Even (S.sum (fun x ↦ x) + d))
    (hB : B ⊆ S) (hsumB : B.sum (fun x ↦ x) = d) (hb : b ∈ B)
    (hmax : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) = d → ∀ x ∈ D, x ≤ b)
    (hw : w ∈ S \ B) (hbw : b < w) (hwd : w < d)
    (hgap : ∀ D : Finset ℕ, D ⊆ S → D.sum (fun x ↦ x) ≠ d - w)
    (hcard : ((S \ B).erase w).card ≤ 3)
    (hresloss : (afterOpening (S \ B) w).value = .loss) :
    (⟨S.erase w, d - w⟩ : Position).value ≠ .loss := by
  by_cases htwo : ((S \ B).erase w).card ≤ 2
  · exact DenseTwoResidual.small_residual_successor_nonloss N d b w S B hS hlarge hdN
      heven hB hsumB hb hmax hw hbw hwd hgap htwo hresloss
  by_cases hterminal : ((S \ B).erase w).sum (fun x ↦ x) < w
  · obtain ⟨D, hDS, hsumD, a, haD, ha⟩ :=
      DenseLossSubsumGap.exists_large_exact_block_member N (Icc 1 N \ S).card d S
        hS le_rfl hlarge hdN
    have hnear : d - (Icc 1 N \ S).card ≤ b := le_trans ha (hmax D hDS hsumD a haD)
    have htsmall : d - w < (Icc 1 N \ S).card := by omega
    exact DenseTerminalNonloss.terminal_gap_successor_nonloss N d w S B hS hlarge hdN
      heven hB hsumB hw hwd htsmall hgap hterminal
  obtain ⟨x, hxB, hxt, hsafe⟩ := three_residual_safe_block_entry N d b w S B hS hlarge hdN
    heven hB hsumB hb hmax hw hbw hwd hgap (by omega) (by omega) hresloss
  have hwB : w ∉ B := (mem_sdiff.mp hw).2
  have hxw : x ≠ w := by intro he; subst x; exact hwB hxB
  have hx : x ∈ S.erase w := mem_erase.mpr ⟨hxw, hB hxB⟩
  have hcatch : ¬ (S.erase w).sum (fun y ↦ y) < d - w := by
    have hh := single_le_sum (fun y _ ↦ Nat.zero_le y) hx
    change x ≤ (S.erase w).sum (fun y ↦ y) at hh
    omega
  intro hloss
  exact hsafe (Position.move_outcome_eq_loss_of_value_eq_loss _ hx hcatch hloss)

end CatchUp.DenseThreeResidual
