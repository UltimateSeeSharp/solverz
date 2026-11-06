module

public import SignedDifferenceSets.Contraction

/-!
# The square condition (C1)

An SDS `D` with parameters (v, k, λ) has `(∑ₓ D x)² = k + λ (v − 1)`: contract along the
zero map to `Unit`, whose one fibre is all of `G`. So `k + λ (v − 1)` is a perfect square.
-/

@[expose] public section

namespace SignedDifferenceSets

variable {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ} {lam : ℤ} {D : G → SignType}

/-- C1: the sum of an SDS squares to `k + λ (v − 1)`. -/
theorem IsSDS.sum_sq (hD : IsSDS k lam D) :
    (∑ x, (D x : ℤ)) ^ 2 = k + lam * ((Fintype.card G : ℤ) - 1) := by
  have h := hD.contract_sq (0 : G →+ Unit)
  have hc : contract (0 : G →+ Unit) D () = ∑ x, (D x : ℤ) := by
    simp [contract]
  have hf : (fibre (0 : G →+ Unit) 0).card = Fintype.card G := by
    simp [fibre]
  have hpos : 1 ≤ Fintype.card G := Fintype.card_pos
  rw [Fintype.sum_unique, hc, hf] at h
  rw [sq, h, Nat.cast_sub hpos, Nat.cast_one]

/-- C1: `k + λ (v − 1)` is a perfect square when an SDS exists. -/
theorem HasSDS.isSquare (h : HasSDS G k lam) :
    IsSquare ((k : ℤ) + lam * ((Fintype.card G : ℤ) - 1)) := by
  obtain ⟨D, hD⟩ := h
  exact ⟨∑ x, (D x : ℤ), by rw [← hD.sum_sq, sq]⟩

/-- C1 as a rule: no SDS when `k + λ (v − 1)` is not a perfect square. -/
theorem not_hasSDS_of_not_isSquare
    (h : ¬ IsSquare ((k : ℤ) + lam * ((Fintype.card G : ℤ) - 1))) : ¬ HasSDS G k lam :=
  fun hG => h hG.isSquare

end SignedDifferenceSets
