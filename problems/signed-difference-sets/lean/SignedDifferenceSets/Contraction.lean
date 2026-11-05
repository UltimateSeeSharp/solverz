module

public import SignedDifferenceSets.Statement

/-!
# Contraction to a quotient (F3)

Push an SDS `D` on `G` along a homomorphism `φ : G →+ H`: the coset sums
`a h = ∑_{φ x = h} D x` satisfy `∑_h a h · a (h + g') = λ · #φ⁻¹(g')` for `g' ≠ 0`, and
`|a h| ≤ #φ⁻¹(h)`. A case dies when no integer vector on `H` meets these.
-/

@[expose] public section

namespace SignedDifferenceSets

variable {G H : Type*} [AddCommGroup G] [Fintype G]
  [AddCommGroup H] [Fintype H] [DecidableEq H]

/-- The coset sums of `D` along `φ`. -/
def contract (φ : G →+ H) (D : G → SignType) (h : H) : ℤ :=
  ∑ x ∈ Finset.univ.filter (fun x => φ x = h), (D x : ℤ)

/-- The fibre of `φ` over `h`. -/
def fibre (φ : G →+ H) (h : H) : Finset G := Finset.univ.filter (fun x => φ x = h)

omit [Fintype H] in
theorem abs_contract_le (φ : G →+ H) (D : G → SignType) (h : H) :
    |contract φ D h| ≤ (fibre φ h).card := by
  unfold contract fibre
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rcases D x with _ | _ | _ <;> simp

/-- The autocorrelation of the coset sums at any `g'` counts the pairs `(x, x + g)` with
`φ g = g'`. -/
theorem contract_autocorr_eq (D : G → SignType) (φ : G →+ H) (g' : H) :
    ∑ h, contract φ D h * contract φ D (h + g') =
      ∑ g ∈ fibre φ g', ∑ x, (D x : ℤ) * (D (x + g) : ℤ) := by
  simp only [contract, Finset.sum_mul_sum, fibre]
  calc ∑ h, ∑ x ∈ Finset.univ.filter (fun x => φ x = h),
        ∑ y ∈ Finset.univ.filter (fun y => φ y = h + g'), (D x : ℤ) * D y
      = ∑ x, ∑ y ∈ Finset.univ.filter (fun y => φ y = φ x + g'), (D x : ℤ) * D y := by
        rw [← Finset.sum_fiberwise Finset.univ (fun x => φ x)
          (fun x => ∑ y ∈ Finset.univ.filter (fun y => φ y = φ x + g'), (D x : ℤ) * D y)]
        refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun x hx => ?_
        rw [(Finset.mem_filter.1 hx).2]
    _ = ∑ x, ∑ g ∈ Finset.univ.filter (fun g => φ g = g'), (D x : ℤ) * D (x + g) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        refine Finset.sum_nbij' (fun y => y - x) (fun g => x + g) ?_ ?_ ?_ ?_ ?_ <;>
          intro a ha <;> simp_all [map_sub, add_sub_cancel_left]
    _ = ∑ g ∈ Finset.univ.filter (fun g => φ g = g'), ∑ x, (D x : ℤ) * D (x + g) :=
        Finset.sum_comm

/-- F3: the autocorrelation of the coset sums at `g' ≠ 0` is `λ` times the fibre size. -/
theorem IsSDS.contract_autocorr {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) (g' : H) (hg' : g' ≠ 0) :
    ∑ h, contract φ D h * contract φ D (h + g') = lam * (fibre φ g').card := by
  rw [contract_autocorr_eq, Finset.sum_congr rfl fun g hg => hD.2 g ?_]
  · simp [mul_comm]
  · rintro rfl
    exact hg' ((Finset.mem_filter.1 hg).2.symm.trans (map_zero φ))

/-- F3 at shift `0`: the coset sums have square sum `k + λ (#ker φ − 1)`. -/
theorem IsSDS.contract_sq {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) :
    ∑ h, contract φ D h * contract φ D h = k + lam * ((fibre φ 0).card - 1 : ℕ) := by
  classical
  have h0 := contract_autocorr_eq D φ 0
  simp only [add_zero] at h0
  have hmem : (0 : G) ∈ fibre φ 0 := by simp [fibre]
  have hself : ∑ x, (D x : ℤ) * D (x + 0) = k := by
    simp only [add_zero]
    rw [← hD.1, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    cases D x <;> simp
  rw [h0, ← Finset.add_sum_erase _ _ hmem, hself,
    Finset.sum_congr rfl fun g hg => hD.2 g (Finset.ne_of_mem_erase hg), Finset.sum_const,
    Finset.card_erase_of_mem hmem]
  simp [mul_comm]

end SignedDifferenceSets
