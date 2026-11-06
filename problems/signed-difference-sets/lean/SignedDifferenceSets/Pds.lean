module

public import SignedDifferenceSets.Statement

/-!
# Partial difference sets with λ′ − μ = 2 give signed difference sets (C11)

A partial difference set (PDS) `P` in `G`: `−P = P`, `0 ∉ P`, and every `g ≠ 0` is a
difference `x − y` of two elements of `P` in `λ′` ways if `g ∈ P`, in `μ` ways otherwise.
If `λ′ − μ = 2`, then `P − {0}` (`P` marked `+1`, the identity `−1`) is an SDS with
parameters (|G|, |P| + 1, μ): its signed count at `g ≠ 0` is the PDS count
− `[g ∈ P]` − `[−g ∈ P]`. In group-ring terms
(P − 1)(P − 1)⁻¹ = P² − 2P + 1 = (|P| − μ + 1) + (λ′ − μ − 2) P + μ G.
-/

@[expose] public section

open scoped Pointwise

namespace SignedDifferenceSets

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- `P` is a partial difference set with parameters (λ′, μ): `−P = P`, `0 ∉ P`, and every
`g ≠ 0` is `x − y` for exactly `λ′` pairs `(x, y) ∈ P × P` if `g ∈ P`, for `μ` pairs if not. -/
def IsPDS (P : Finset G) (lam' mu : ℕ) : Prop :=
  -P = P ∧ (0 : G) ∉ P ∧
    ∀ g : G, g ≠ 0 →
      ((P ×ˢ P).filter fun p => p.1 - p.2 = g).card = if g ∈ P then lam' else mu

/-- `P − {0}`: `+1` on `P`, `−1` at the identity, `0` elsewhere. -/
def minusZero (P : Finset G) (x : G) : SignType :=
  if x ∈ P then 1 else if x = 0 then -1 else 0

/-- The pairs `(x, y) ∈ P × P` with `x − y = g` match the `y ∈ P` with `y + g ∈ P`. -/
theorem card_pairs_sub_eq (P : Finset G) (g : G) :
    ((P ×ˢ P).filter fun p => p.1 - p.2 = g).card =
      (Finset.univ.filter fun y => y ∈ P ∧ y + g ∈ P).card := by
  refine Finset.card_nbij' (fun p => p.2) (fun y => (y + g, y)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq,
      Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact ⟨h2, by rw [← h3]; simpa using h1⟩
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_product, Set.mem_ofPred_eq,
      Finset.mem_univ, true_and] at hy ⊢
    exact ⟨⟨hy.2, hy.1⟩, by abel⟩
  · intro p hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp
    ext <;> simp [← hp.2]
  · intro y _
    rfl

/-- C11: if `P` is a PDS with λ′ − μ = 2, then `P − {0}` is an SDS with parameters
(|G|, |P| + 1, μ). -/
theorem IsPDS.isSDS_minusZero {P : Finset G} {lam' mu : ℕ} (hP : IsPDS P lam' mu)
    (hdiff : lam' = mu + 2) : IsSDS (P.card + 1) mu (minusZero P) := by
  obtain ⟨hneg, h0, hcount⟩ := hP
  refine ⟨?_, fun g hg => ?_⟩
  · have : (Finset.univ.filter fun x => minusZero P x ≠ 0) = insert 0 P := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      unfold minusZero
      by_cases hx : x = 0
      · subst hx
        simp [h0]
      · by_cases hxP : x ∈ P <;> simp [hx, hxP]
    rw [this, Finset.card_insert_of_notMem h0]
  · have hsymm : -g ∈ P ↔ g ∈ P := by
      rw [← Finset.mem_neg', hneg]
    have hterm : ∀ x : G, ((minusZero P x : ℤ) * (minusZero P (x + g) : ℤ)) =
        (if x ∈ P ∧ x + g ∈ P then 1 else 0) - (if x = -g then (if g ∈ P then 1 else 0) else 0)
          - (if x = 0 then (if g ∈ P then 1 else 0) else 0) := by
      intro x
      by_cases hx0 : x = 0
      · subst hx0
        have : (0 : G) ≠ -g := fun h => hg (neg_eq_zero.mp h.symm)
        by_cases hgP : g ∈ P <;> simp [minusZero, h0, hgP, this, hg]
      by_cases hxg : x = -g
      · subst hxg
        by_cases hgP : g ∈ P <;> simp [minusZero, h0, hgP, hsymm, hx0]
      have hxg' : x + g ≠ 0 := fun h => hxg (eq_neg_of_add_eq_zero_left h)
      by_cases hxP : x ∈ P <;> by_cases hxgP : x + g ∈ P <;>
        simp [minusZero, hxP, hxgP, hx0, hxg, hxg']
    rw [Finset.sum_congr rfl fun x _ => hterm x]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_boole]
    rw [← card_pairs_sub_eq, hcount g hg]
    by_cases hgP : g ∈ P
    · simp only [hgP, ite_true, hdiff]
      push_cast
      ring
    · simp [hgP]

/-- C11: a PDS `P` in `G` with λ′ − μ = 2 gives an SDS with parameters (|G|, |P| + 1, μ). -/
theorem IsPDS.hasSDS {P : Finset G} {lam' mu : ℕ} (hP : IsPDS P lam' mu)
    (hdiff : lam' = mu + 2) : HasSDS G (P.card + 1) mu :=
  ⟨minusZero P, hP.isSDS_minusZero hdiff⟩

end SignedDifferenceSets
