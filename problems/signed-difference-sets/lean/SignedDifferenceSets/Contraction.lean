module

public import SignedDifferenceSets.Statement

/-!
# Contraction to a quotient (C3)

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

/-- C3: the autocorrelation of the coset sums at `g' ≠ 0` is `λ` times the fibre size. -/
theorem IsSDS.contract_autocorr {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) (g' : H) (hg' : g' ≠ 0) :
    ∑ h, contract φ D h * contract φ D (h + g') = lam * (fibre φ g').card := by
  rw [contract_autocorr_eq, Finset.sum_congr rfl fun g hg => hD.2 g ?_]
  · simp [mul_comm]
  · rintro rfl
    exact hg' ((Finset.mem_filter.1 hg).2.symm.trans (map_zero φ))

/-- C3 at shift `0`: the coset sums have square sum `k + λ (#ker φ − 1)`. -/
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

omit [Fintype H] in
/-- Every fibre of a surjective homomorphism is as large as the kernel. -/
theorem card_fibre {φ : G →+ H} (hφ : Function.Surjective φ) (h : H) :
    (fibre φ h).card = (fibre φ 0).card := by
  obtain ⟨x, rfl⟩ := hφ h
  refine Finset.card_bij (fun y _ => y - x) (fun y hy => ?_) (fun a _ b _ hab => ?_)
    (fun z hz => ⟨z + x, ?_, by simp⟩)
  · simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [map_sub, hy, sub_self]
  · simpa using hab
  · simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rw [map_add, hz, zero_add]

/-- The fibres of a surjective homomorphism have `|G| / |H|` elements. -/
theorem card_fibre_eq {φ : G →+ H} (hφ : Function.Surjective φ) {c : ℕ}
    (hc : Fintype.card G = c * Fintype.card H) (h : H) : (fibre φ h).card = c := by
  have hsum := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := φ) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ] at hsum
  change Fintype.card G = ∑ b, (fibre φ b).card at hsum
  rw [Finset.sum_congr rfl fun h' _ => card_fibre hφ h'] at hsum
  have hpos : 0 < Fintype.card H := Fintype.card_pos
  rw [card_fibre hφ h]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [← hsum, hc, mul_comm])

theorem abs_sign_eq (s : SignType) : |(s : ℤ)| = if s = 0 then 0 else 1 := by
  cases s <;> simp

theorem IsSDS.sum_abs {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D) :
    ∑ x, |(D x : ℤ)| = k := by
  rw [← hD.1, Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [abs_sign_eq]; split_ifs <;> simp_all

theorem sum_fibre (φ : G →+ H) (f : G → ℤ) : ∑ h, ∑ x ∈ fibre φ h, f x = ∑ x, f x :=
  Finset.sum_fiberwise _ _ _

/-- The coset sums' absolute values add up to at most `k`. -/
theorem IsSDS.sum_abs_contract_le {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) : ∑ h, |contract φ D h| ≤ k := by
  calc ∑ h, |contract φ D h|
      ≤ ∑ h, ∑ x ∈ fibre φ h, |(D x : ℤ)| :=
        Finset.sum_le_sum fun h _ => Finset.abs_sum_le_sum_abs _ _
    _ = k := by rw [sum_fibre, hD.sum_abs]

/-- `k` and the coset sums' absolute values have the same parity. -/
theorem IsSDS.sum_abs_contract_parity {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) : ((k : ℤ) - ∑ h, |contract φ D h|) % 2 = 0 := by
  have hk : (k : ℤ) = ∑ h, ∑ x ∈ fibre φ h, |(D x : ℤ)| := by rw [sum_fibre, hD.sum_abs]
  rw [hk, ← Finset.sum_sub_distrib, ← Int.even_iff]
  refine Finset.even_sum _ fun h _ => ?_
  have e : ∑ x ∈ fibre φ h, |(D x : ℤ)| - |contract φ D h| =
      ∑ x ∈ fibre φ h, (|(D x : ℤ)| - D x) + (contract φ D h - |contract φ D h|) := by
    rw [Finset.sum_sub_distrib]; unfold contract fibre; ring
  rw [e]
  refine Even.add (Finset.even_sum _ fun x _ => ?_) ?_
  · cases D x <;> simp
  · rcases abs_choice (contract φ D h) with h' | h' <;> rw [h']
    · simp
    · exact ⟨contract φ D h, by ring⟩

end SignedDifferenceSets
