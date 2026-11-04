/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CertificateComplexity.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.CertificateSoundness
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Explicit strategy certificate size

The full checker language has only genuinely terminal leaves. A finite family of
paired-game synchronization states closed under deletion contains every subset.
This is a representation-size claim, not a lower bound on mathematical proof size.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateComplexity

open CatchUp CertificateChecker

/-- The actual interval root, before the forced single opening pick. -/
def initialPosition (N : ℕ) : GamePosition :=
  ⟨⟨Finset.Icc 1 N, 0⟩, .p1⟩

/-- Full, checked nonloss certificates from the interval root. -/
def InitialCertificate (N : ℕ) (player : Player) (dag : StrategyDAG) : Prop :=
  DAGValid dag ∧ dag.gameSize = N ∧ dag.player = player ∧
    toGamePosition dag.gameSize dag.root = initialPosition N

/-- Existence is a separate proposition, not an infinite node-count convention. -/
def CertificateExists (N : ℕ) (player : Player) : Prop :=
  ∃ dag, InitialCertificate N player dag

theorem exists_certificate_count (N : ℕ) (player : Player)
    (h : CertificateExists N player) :
    ∃ n, ∃ dag, InitialCertificate N player dag ∧ dag.nodes.length = n := by
  obtain ⟨dag, hdag⟩ := h
  exact ⟨dag.nodes.length, dag, hdag, rfl⟩

/-- Minimum listed-node count, defined only when a full initial certificate exists. -/
noncomputable def minimumNodes (N : ℕ) (player : Player)
    (h : CertificateExists N player) : ℕ := by
  classical
  exact Nat.find (exists_certificate_count N player h)

/-- The minimum is realized by a valid certificate; absent certificates are not assigned a size. -/
theorem minimumNodes_realized (N : ℕ) (player : Player) (h : CertificateExists N player) :
    ∃ dag, InitialCertificate N player dag ∧ dag.nodes.length = minimumNodes N player h := by
  classical
  exact Nat.find_spec (exists_certificate_count N player h)

/-- Every witness count is an upper bound on the minimum, not an exact-minimum assertion. -/
theorem minimumNodes_le (N : ℕ) (player : Player) (h : CertificateExists N player)
    (dag : StrategyDAG) (hdag : InitialCertificate N player dag) :
    minimumNodes N player h ≤ dag.nodes.length := by
  classical
  exact Nat.find_min' (exists_certificate_count N player h) ⟨dag, hdag, rfl⟩

/-- The first pick switches to player two, including the equality convention. -/
theorem initial_after_pick (N x : ℕ) :
    (initialPosition N).afterPick x =
      ⟨⟨(Finset.Icc 1 N).erase x, x⟩, .p2⟩ := by
  simp [initialPosition, GamePosition.afterPick, Position.afterPick, Player.other]

section Deletion

variable {α : Type*} [DecidableEq α]

/-- Synchronization-state closure forced by the mate-response game. -/
def DeletionClosed (C : Finset (Finset α)) : Prop :=
  ∀ S ∈ C, ∀ x ∈ S, S.erase x ∈ C

/-- Deletion closure allows deletion of any prescribed finite set. -/
theorem sdiff_mem_of_deletionClosed (C : Finset (Finset α))
    (hC : DeletionClosed C) (S : Finset α) (hS : S ∈ C) (T : Finset α) :
    S \ T ∈ C := by
  induction T using Finset.induction_on with
  | empty => simpa using hS
  | @insert x T hx ih =>
      have heq : S \ insert x T = (S \ T).erase x := by
        ext a
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      rw [heq]
      by_cases hm : x ∈ S \ T
      · exact hC _ ih _ hm
      · simpa [Finset.erase_eq_of_notMem hm] using ih

/-- Every remaining-pair subset must occur in any deletion-closed certificate. -/
theorem powerset_subset_of_deletionClosed (C : Finset (Finset α))
    (hC : DeletionClosed C) (S : Finset α) (hS : S ∈ C) :
    S.powerset ⊆ C := by
  intro T hT
  have hsub := Finset.mem_powerset.mp hT
  simpa [Finset.sdiff_sdiff_eq_self hsub] using
    sdiff_mem_of_deletionClosed C hC S hS (S \ T)

/-- Exponential synchronization-state lower bound for the paired calibration game. -/
theorem exponential_of_deletionClosed (C : Finset (Finset α))
    (hC : DeletionClosed C) (S : Finset α) (hS : S ∈ C) :
    2 ^ S.card ≤ C.card := by
  simpa only [Finset.card_powerset] using
    Finset.card_le_card (powerset_subset_of_deletionClosed C hC S hS)

/-- All subsets themselves form a certificate with exactly the lower-bound size. -/
theorem powerset_deletionClosed (S : Finset α) : DeletionClosed S.powerset := by
  intro T hT x _
  exact Finset.mem_powerset.mpr ((Finset.erase_subset x T).trans
    (Finset.mem_powerset.mp hT))

end Deletion

section Covering

variable {α : Type*} [DecidableEq α]

/-- Covering all small target sets forces many bounded-size deletion sets. -/
theorem target_cover_count (S : Finset α) (C : Finset (Finset α)) (t a : ℕ)
    (hcover : ∀ T ∈ S.powersetCard t, ∃ A ∈ C, T ⊆ A)
    (hsize : ∀ A ∈ C, A.card ≤ a) :
    S.card.choose t ≤ C.card * a.choose t := by
  have hsub : S.powersetCard t ⊆ C.biUnion (fun A => A.powersetCard t) := by
    intro T hT
    obtain ⟨A, hA, hTA⟩ := hcover T hT
    exact Finset.mem_biUnion.mpr ⟨A, hA,
      Finset.mem_powersetCard.mpr ⟨hTA, (Finset.mem_powersetCard.mp hT).2⟩⟩
  calc
    S.card.choose t = (S.powersetCard t).card := (Finset.card_powersetCard _ _).symm
    _ ≤ (C.biUnion (fun A => A.powersetCard t)).card := Finset.card_le_card hsub
    _ ≤ ∑ A ∈ C, (A.powersetCard t).card := Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ C, a.choose t := Finset.sum_le_sum fun A hA => by
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_choose t (hsize A hA)
    _ = C.card * a.choose t := by simp

/-- Doubling the available labels more than doubles each factor in a fixed-size choice. -/
theorem two_pow_mul_choose_le (n a t : ℕ) (hna : 2 * a ≤ n) :
    2 ^ t * a.choose t ≤ n.choose t := by
  have hfall : ∀ t, 2 ^ t * a.descFactorial t ≤ n.descFactorial t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        by_cases hat : a ≤ t
        · simp [Nat.descFactorial_succ, Nat.sub_eq_zero_of_le hat]
        · have hfactor : 2 * (a - t) ≤ n - t := by omega
          calc
            2 ^ (t + 1) * a.descFactorial (t + 1) =
                (2 * (a - t)) * (2 ^ t * a.descFactorial t) := by
                  rw [pow_succ, Nat.descFactorial_succ]
                  ring
            _ ≤ (n - t) * n.descFactorial t := Nat.mul_le_mul hfactor ih
            _ = n.descFactorial (t + 1) := (Nat.descFactorial_succ _ _).symm
  have h := hfall t
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h
  have h' : t.factorial * (2 ^ t * a.choose t) ≤ t.factorial * n.choose t := by
    simpa only [Nat.mul_left_comm] using h
  exact Nat.le_of_mul_le_mul_left h' (Nat.factorial_pos t)

/-- The covering argument remains exponential after allowing many targets to share a state. -/
theorem target_cover_exponential (S : Finset α) (C : Finset (Finset α)) (t a : ℕ)
    (hta : t ≤ a) (has : 2 * a ≤ S.card)
    (hcover : ∀ T ∈ S.powersetCard t, ∃ A ∈ C, T ⊆ A)
    (hsize : ∀ A ∈ C, A.card ≤ a) :
    2 ^ t ≤ C.card := by
  have h := (two_pow_mul_choose_le S.card a t has).trans
    (target_cover_count S C t a hcover hsize)
  exact Nat.le_of_mul_le_mul_right h (Nat.choose_pos hta)

end Covering

end CatchUpSearch.CertificateComplexity
