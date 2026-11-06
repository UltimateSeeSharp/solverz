module

public import SignedDifferenceSets.Statement

/-!
# C21's statement, as a proposition

`MaRule` is C21 (Ma's lemma on a mixed quotient `ZMod (r p) × K`) in the form the row checks
use: an SDS's coset sums on such a quotient, with `p` self-conjugate on `K`, `p^e ∣ k − λ`,
`2b ≤ e` and `2c < p^b`, cannot exist when `x ↦ x − 1` behaves like `ζ − 1` above `p` in every
ring where `∑_{l<p} (x^r)^l = 0` (`p = (x − 1)^((p−1) r) y` and `(x − 1)^((p−1) r) = p z`).
Its proof is `maRule` (`MaLemma.lean`); the rows use only this statement.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- C21, stated for every group and quotient. -/
def MaRule : Prop :=
  ∀ (G K : Type) [AddCommGroup G] [Fintype G] [AddCommGroup K] [Fintype K] [DecidableEq K]
    (p r i e b c k : ℕ) (lam : ℤ) [Fact p.Prime] [NeZero (r * p)]
    (φ : G →+ ZMod (r * p) × K), Function.Surjective φ →
    Fintype.card G = c * Fintype.card (ZMod (r * p) × K) → 0 < r → 0 < i →
    (∀ x : K, p ^ i • x = -x) → (p : ℤ) ^ e ∣ (k : ℤ) - lam → (k : ℤ) ≠ lam → 2 * b ≤ e →
    2 * c < p ^ b →
    (∀ (S : Type) [CommRing S] (x : S), ∑ l ∈ Finset.range p, (x ^ r) ^ l = 0 →
      ∃ y z : S, (p : S) = (x - 1) ^ ((p - 1) * r) * y ∧ (x - 1) ^ ((p - 1) * r) = p * z) →
    ¬ HasSDS G k lam

end SignedDifferenceSets
