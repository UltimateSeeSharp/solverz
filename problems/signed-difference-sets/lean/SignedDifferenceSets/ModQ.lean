module

public import SignedDifferenceSets.Multiplier

/-!
# C24: mod-`q` vanishing

For an SDS `D` with `q ∣ n = k − λ` and a character `ψ` of `G` into a field of characteristic `q`
with `Σ ψ = 0`, `ψ(D) · ψ(D^(−1)) = 0` (`IsSDS.charSum_mul_charSum_neg`): `DD^(−1) = n + λG` maps
to `n + λ Σ ψ = 0`. So `ψ(D) = 0` or `ψ(D^(−1)) = 0` (`IsSDS.charSum_eq_zero_or`).
-/

@[expose] public section

namespace SignedDifferenceSets

variable {G K : Type*} [AddCommGroup G] [Fintype G] [Field K]

/-- `ψ(D) = Σ_x D(x) ψ(x)` for a character `ψ : Multiplicative G →* K`. -/
def charSum (ψ : Multiplicative G →* K) (D : G → SignType) : K :=
  ∑ x, ((D x : ℤ) : K) * ψ (Multiplicative.ofAdd x)

/-- C24: `ψ(D) ψ(D^(−1)) = 0` when `q ∣ k − λ`, `K` has characteristic `q` and `Σ ψ = 0`. -/
theorem IsSDS.charSum_mul_charSum_neg [DecidableEq G] {k : ℕ} {lam : ℤ} {D : G → SignType}
    (hD : IsSDS k lam D) (q : ℕ) [CharP K q] (hq : (q : ℤ) ∣ (k : ℤ) - lam)
    (ψ : Multiplicative G →* K) (hψ : ∑ x : G, ψ (Multiplicative.ofAdd x) = 0) :
    charSum ψ D * charSum ψ (fun x => D (-x)) = 0 := by
  have hψadd : ∀ y g : G, ψ (Multiplicative.ofAdd (y + g)) * ψ (Multiplicative.ofAdd (-y)) =
      ψ (Multiplicative.ofAdd g) := by
    intro y g
    rw [← map_mul, ← ofAdd_add]
    congr 2
    abel
  have hn : (((k : ℤ) - lam : ℤ) : K) = 0 := by
    obtain ⟨c, hc⟩ := hq
    rw [hc, Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero, zero_mul]
  have hneg : charSum ψ (fun x => D (-x)) =
      ∑ y, ((D y : ℤ) : K) * ψ (Multiplicative.ofAdd (-y)) := by
    unfold charSum
    exact Fintype.sum_equiv (Equiv.neg G) _ _ fun x => by simp
  rw [hneg, charSum, Finset.sum_mul_sum, Finset.sum_comm]
  have hre : ∀ y : G, ∑ x, ((D x : ℤ) : K) * ψ (Multiplicative.ofAdd x) *
      (((D y : ℤ) : K) * ψ (Multiplicative.ofAdd (-y))) =
      ∑ g, ψ (Multiplicative.ofAdd g) * (((D y : ℤ) * (D (y + g) : ℤ) : ℤ) : K) := by
    intro y
    rw [← Fintype.sum_equiv (Equiv.addLeft y) (fun g => ((D (y + g) : ℤ) : K) *
      ψ (Multiplicative.ofAdd (y + g)) * (((D y : ℤ) : K) * ψ (Multiplicative.ofAdd (-y))))
      _ fun g => rfl]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hψadd y g, Int.cast_mul]
    ring
  rw [Finset.sum_congr rfl fun y _ => hre y, Finset.sum_comm]
  have hac : ∀ g : G, ∑ y, ψ (Multiplicative.ofAdd g) * (((D y : ℤ) * (D (y + g) : ℤ) : ℤ) : K) =
      ψ (Multiplicative.ofAdd g) * (((if g = 0 then (k : ℤ) - lam else 0) + lam : ℤ) : K) := by
    intro g
    rw [← Finset.mul_sum, ← Int.cast_sum, hD.autocorr g]
  rw [Finset.sum_congr rfl fun g _ => hac g]
  simp only [Int.cast_add, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hψ, zero_mul,
    add_zero]
  rw [Finset.sum_eq_single (0 : G) (fun g _ hg => by rw [if_neg hg, Int.cast_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, hn, mul_zero]

/-- C24 as a split: `ψ(D) = 0` or `ψ(D^(−1)) = 0`. -/
theorem IsSDS.charSum_eq_zero_or [DecidableEq G] {k : ℕ} {lam : ℤ} {D : G → SignType}
    (hD : IsSDS k lam D) (q : ℕ) [CharP K q] (hq : (q : ℤ) ∣ (k : ℤ) - lam)
    (ψ : Multiplicative G →* K) (hψ : ∑ x : G, ψ (Multiplicative.ofAdd x) = 0) :
    charSum ψ D = 0 ∨ charSum ψ (fun x => D (-x)) = 0 :=
  mul_eq_zero.1 (hD.charSum_mul_charSum_neg q hq ψ hψ)

end SignedDifferenceSets
