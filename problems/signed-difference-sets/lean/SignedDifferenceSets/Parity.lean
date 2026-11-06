module

public import SignedDifferenceSets.Statement

/-!
# Rule A3: support parity (C8)

Let `d` be the number of unmarked elements. Mod 2, `∑ₓ D x · D (x + g)` counts the `x` with
`x` and `x + g` both marked, which is `v − 2d` plus the number with both unmarked. With `v`
odd and `λ` even that number is odd, so every `g ≠ 0` is a difference of two unmarked
elements, and `d (d − 1) ≥ v − 1`.
-/

@[expose] public section

namespace SignedDifferenceSets

variable {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ} {lam : ℤ} {D : G → SignType}

/-- The unmarked elements of `D`. -/
def zeros (D : G → SignType) : Finset G := Finset.univ.filter fun x => D x = 0

/-- An SDS leaves `v − k` elements unmarked. -/
theorem IsSDS.card_zeros (hD : IsSDS k lam D) : (zeros D).card = Fintype.card G - k := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x => D x ≠ 0)
  have hz : Finset.univ.filter (fun x => ¬ D x ≠ 0) = zeros D := by simp [zeros]
  rw [hD.1, Finset.card_univ, hz] at h
  omega

/-- With `v` odd and `λ` even, every `g ≠ 0` joins two unmarked elements. -/
theorem IsSDS.exists_zeros_of_parity (hD : IsSDS k lam D) (hv : Odd (Fintype.card G))
    (hlam : Even lam) {g : G} (hg : g ≠ 0) : ∃ x, D x = 0 ∧ D (x + g) = 0 := by
  classical
  set u : G → ℤ := fun x => if D x = 0 then 1 else 0 with hu
  have key : ∀ a b : SignType, Even ((a : ℤ) * b - (if a = 0 then 1 else 0) *
      (if b = 0 then 1 else 0) + (if a = 0 then 1 else 0) + (if b = 0 then 1 else 0) - 1) := by
    intro a b
    cases a <;> cases b <;> decide
  have hsum : Even (∑ x, ((D x : ℤ) * D (x + g) - u x * u (x + g) + u x + u (x + g) - 1)) :=
    Finset.even_sum _ fun x _ => key (D x) (D (x + g))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  have hshift : ∑ x, u (x + g) = ∑ x, u x :=
    Fintype.sum_equiv (Equiv.addRight g) _ _ (fun _ => rfl)
  have hcount : ∑ x, u x = (zeros D).card := by
    simp only [hu, zeros]
    rw [Finset.sum_boole]
  rw [hD.2 g hg, hshift, hcount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hsum
  by_contra hne
  have hN : ∑ x, u x * u (x + g) = 0 := Finset.sum_eq_zero fun x _ => by
    simp only [hu]
    split_ifs with h1 h2 <;> simp_all
  rw [hN] at hsum
  obtain ⟨r, hr⟩ := hsum
  obtain ⟨s, hs⟩ := hlam
  obtain ⟨t, ht⟩ := hv
  rw [ht] at hr
  push_cast at hr
  omega

/-- Rule A3's condition on (v, k, λ): `v` odd, `λ` even, `d (d − 1) < v − 1` for
`d = v − k` (`d = 0` when `k ≥ v`). -/
def SupportParity (v k : ℕ) (lam : ℤ) : Prop :=
  Odd v ∧ Even lam ∧ (v - k) * (v - k - 1) < v - 1

instance (v k : ℕ) (lam : ℤ) : Decidable (SupportParity v k lam) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- C8 (rule A3): no SDS when `v` is odd, `λ` even and `d (d − 1) < v − 1`, `d = v − k`. -/
theorem not_hasSDS_of_supportParity {v : ℕ} (hG : Fintype.card G = v)
    (h : SupportParity v k lam) : ¬ HasSDS G k lam := by
  classical
  subst hG
  obtain ⟨hv, hlam, hd⟩ := h
  rintro ⟨D, hD⟩
  have hsub : Finset.univ.erase (0 : G) ⊆
      (zeros D).offDiag.image (fun p => p.2 - p.1) := by
    intro g hg
    have hg0 : g ≠ 0 := Finset.ne_of_mem_erase hg
    obtain ⟨x, hx, hxg⟩ := hD.exists_zeros_of_parity hv hlam hg0
    refine Finset.mem_image.2 ⟨(x, x + g), ?_, by simp⟩
    simp [Finset.mem_offDiag, zeros, hx, hxg, hg0]
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Finset.offDiag_card,
    hD.card_zeros] at h1
  have hm := Nat.mul_sub_one (Fintype.card G - k) (Fintype.card G - k)
  generalize Fintype.card G - k = d at h1 hd hm
  omega

/-! Tests: the rule fires on (5, 4, 0) and (7, 5, 2), and not where an SDS exists. -/

example : ¬ HasSDS (ZMod 5) 4 0 := not_hasSDS_of_supportParity (ZMod.card 5) (by decide)

example : SupportParity 7 5 2 := by decide

/-- CW(7, 4) and a (13, 9, 6) set exist: the equality cases. -/
example : ¬ SupportParity 7 4 0 ∧ ¬ SupportParity 13 9 6 := by decide

/-- The (5, 4, −1) SDS exists: `λ` odd. -/
example : ¬ SupportParity 5 4 (-1) := by decide

end SignedDifferenceSets
