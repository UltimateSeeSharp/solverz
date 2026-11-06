module

public import SignedDifferenceSets.Square

/-!
# Real characters on an elementary abelian 2-quotient (C17)

Let `φ : G →+ H` be onto a group with `h + h = 0` of order `2^r`. Its complex characters `ψ`
are `±1`-valued, so `ψ(D) = ∑ₓ D x · ψ (φ x)` is an integer, `ψ(D)² = k − λ` for `ψ ≠ 0` (a),
and `∑_ψ ψ(D) = 2^r · a₀` with `a₀` the coset sum at `0` (b). With `k − λ = m²` each
`ψ(D) = ±m`, so `2^r ∣ s' + m T` for `s' = ∑ D = ±s` (C1) and `T` a sum of `2^r − 1` signs:
odd, `|T| ≤ 2^r − 1`. No SDS when no such `s'`, `T` exist (c).
-/

@[expose] public section

namespace SignedDifferenceSets

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] {k : ℕ} {lam : ℤ}
  {D : G → SignType}

/-- The character sum `ψ(D) = ∑ₓ D x · ψ (φ x)`. -/
noncomputable def charSum (φ : G →+ H) (D : G → SignType) (ψ : AddChar H ℂ) : ℂ :=
  ∑ x, ((D x : ℤ) : ℂ) * ψ (φ x)

/-- On a group with `h + h = 0`, characters square to `1`. -/
theorem mul_self_apply_eq_one (hH : ∀ h : H, h + h = 0) (ψ : AddChar H ℂ) (h : H) :
    ψ h * ψ h = 1 := by
  rw [← AddChar.map_add_eq_mul, hH, AddChar.map_zero_eq_one]

open scoped Classical in
/-- The value `ψ h = ±1` as an integer. -/
noncomputable def charSign (ψ : AddChar H ℂ) (h : H) : ℤ := if ψ h = 1 then 1 else -1

theorem charSign_cast (hH : ∀ h : H, h + h = 0) (ψ : AddChar H ℂ) (h : H) :
    (charSign ψ h : ℂ) = ψ h := by
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  rcases mul_self_eq_one_iff.1 (mul_self_apply_eq_one hH ψ h) with h1 | h1 <;>
    simp [charSign, h1, hne]

/-- `ψ(D)` as an integer. -/
noncomputable def charSumInt (φ : G →+ H) (D : G → SignType) (ψ : AddChar H ℂ) : ℤ :=
  ∑ x, (D x : ℤ) * charSign ψ (φ x)

theorem charSumInt_cast (hH : ∀ h : H, h + h = 0) (φ : G →+ H) (D : G → SignType)
    (ψ : AddChar H ℂ) : (charSumInt φ D ψ : ℂ) = charSum φ D ψ := by
  simp only [charSumInt, charSum, Int.cast_sum, Int.cast_mul, charSign_cast hH]

/-- C17 (a): a nontrivial character has `ψ(D)² = k − λ`. -/
theorem IsSDS.charSum_sq (hD : IsSDS k lam D) {φ : G →+ H} (hφ : Function.Surjective φ)
    (hH : ∀ h : H, h + h = 0) {ψ : AddChar H ℂ} (hψ : ψ ≠ 0) :
    charSum φ D ψ ^ 2 = (k : ℂ) - lam := by
  classical
  have hsum : ∑ g, ψ (φ g) = 0 := by
    have hne : ψ.compAddMonoidHom φ ≠ 0 := by
      intro h0
      refine hψ (AddChar.ext _ _ fun h => ?_)
      obtain ⟨g, rfl⟩ := hφ h
      simpa using DFunLike.congr_fun h0 g
    simpa using AddChar.sum_eq_zero_iff_ne_zero.2 hne
  have hpair (x g : G) : ψ (φ x) * ψ (φ (x + g)) = ψ (φ g) := by
    rw [map_add, AddChar.map_add_eq_mul, ← mul_assoc, mul_self_apply_eq_one hH, one_mul]
  have hA (g : G) : ∑ x, ((D x : ℤ) : ℂ) * ((D (x + g) : ℤ) : ℂ) =
      lam + if g = 0 then (k : ℂ) - lam else 0 := by
    split_ifs with hg
    · subst hg
      have hk : ∑ x, (D x : ℤ) * (D (x + 0) : ℤ) = k := by
        simp only [add_zero]
        rw [← hD.1, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        cases D x <;> simp
      rw [show (lam : ℂ) + ((k : ℂ) - lam) = k by ring]
      exact_mod_cast hk
    · rw [add_zero]
      exact_mod_cast hD.2 g hg
  calc charSum φ D ψ ^ 2
      = ∑ x, ∑ y, ((D x : ℤ) : ℂ) * ψ (φ x) * (((D y : ℤ) : ℂ) * ψ (φ y)) := by
        rw [sq, charSum, Finset.sum_mul_sum]
    _ = ∑ x, ∑ g, ((D x : ℤ) : ℂ) * ψ (φ x) * (((D (x + g) : ℤ) : ℂ) * ψ (φ (x + g))) :=
        Finset.sum_congr rfl fun x _ => (Equiv.sum_comp (Equiv.addLeft x) _).symm
    _ = ∑ g, ψ (φ g) * ∑ x, ((D x : ℤ) : ℂ) * ((D (x + g) : ℤ) : ℂ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← hpair x g]
        ring
    _ = (k : ℂ) - lam := by
        simp only [hA, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, zero_mul,
          mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, map_zero,
          AddChar.map_zero_eq_one, one_mul, zero_add]

/-- C17 (b): summed over all characters, `∑_ψ ψ(D) = |H| · a₀`. -/
theorem sum_charSum [Fintype H] [DecidableEq H] (φ : G →+ H) (D : G → SignType) :
    ∑ ψ : AddChar H ℂ, charSum φ D ψ = Fintype.card H * (contract φ D 0 : ℂ) := by
  simp only [charSum]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, AddChar.sum_apply_eq_ite, mul_ite, mul_zero]
  rw [← Finset.sum_filter, contract, Int.cast_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- A sum of signs over `s` has the parity of `#s` and absolute value at most `#s`. -/
theorem sum_signs {ι : Type*} (s : Finset ι) (ε : ι → ℤ) (hε : ∀ i ∈ s, ε i = 1 ∨ ε i = -1) :
    Even (∑ i ∈ s, ε i - s.card) ∧ |∑ i ∈ s, ε i| ≤ s.card := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  constructor
  · rw [← Finset.sum_sub_distrib]
    refine Finset.even_sum _ fun i hi => ?_
    rcases hε i hi with h | h <;> rw [h] <;> norm_num
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rcases hε i hi with h | h <;> simp [h]

/-- C17 (c): no SDS when `k − λ = m²`, `s² = k + λ(v − 1)`, and for a quotient `H` of order
`2^r`, `r > 0`, with `h + h = 0`, `2^r` divides no `s' + m T` with `s' = ±s` and odd `T`,
`|T| ≤ 2^r − 1`. -/
theorem not_hasSDS_of_realChars [Fintype H] {r : ℕ} {φ : G →+ H}
    (hφ : Function.Surjective φ) (hH : ∀ h : H, h + h = 0) (hr : 0 < r)
    (hcard : Fintype.card H = 2 ^ r) {m s : ℤ}
    (hm : m ^ 2 = k - lam) (hs : s ^ 2 = k + lam * ((Fintype.card G : ℤ) - 1))
    (hkill : ∀ s' ∈ [s, -s], ∀ T : ℤ, Odd T → |T| ≤ 2 ^ r - 1 → ¬ (2 : ℤ) ^ r ∣ s' + m * T) :
    ¬ HasSDS G k lam := by
  classical
  rintro ⟨D, hD⟩
  have hs' : (∑ x, (D x : ℤ)) ∈ [s, -s] := by
    have h := hD.sum_sq
    rw [← hs] at h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h <;> simp [h]
  have h0 : charSumInt φ D 0 = ∑ x, (D x : ℤ) := by simp [charSumInt, charSign]
  have hpm (ψ : AddChar H ℂ) (hψ : ψ ≠ 0) : charSumInt φ D ψ = m ∨ charSumInt φ D ψ = -m := by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    have h := hD.charSum_sq hφ hH hψ
    rw [← charSumInt_cast hH] at h
    rw [hm]
    exact_mod_cast h
  let ε : AddChar H ℂ → ℤ := fun ψ => if charSumInt φ D ψ = m then 1 else -1
  have hz (ψ : AddChar H ℂ) (hψ : ψ ≠ 0) : charSumInt φ D ψ = m * ε ψ := by
    by_cases h : charSumInt φ D ψ = m
    · simp [ε, h]
    · simp only [ε, h, ↓reduceIte]
      rw [(hpm ψ hψ).resolve_left h]
      ring
  have hsum : ∑ ψ : AddChar H ℂ, charSumInt φ D ψ = 2 ^ r * contract φ D 0 := by
    have h := sum_charSum φ D
    simp only [← charSumInt_cast hH, hcard] at h
    exact_mod_cast h
  have hT : ∑ ψ ∈ Finset.univ.erase 0, charSumInt φ D ψ =
      m * ∑ ψ ∈ Finset.univ.erase 0, ε ψ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ψ hψ => hz ψ (Finset.ne_of_mem_erase hψ)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : AddChar H ℂ)), h0, hT] at hsum
  obtain ⟨hpar, habs⟩ := sum_signs (Finset.univ.erase (0 : AddChar H ℂ)) ε
    fun ψ _ => by by_cases h : charSumInt φ D ψ = m <;> simp [ε, h]
  have hcardE : ((Finset.univ.erase (0 : AddChar H ℂ)).card : ℤ) = 2 ^ r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, AddChar.card_eq, hcard,
      Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [hcardE] at hpar habs
  have hodd : Odd (∑ ψ ∈ Finset.univ.erase 0, ε ψ) := by
    obtain ⟨a, ha⟩ := hpar
    obtain ⟨b, hb⟩ := (Int.even_pow.2 ⟨even_two, hr.ne'⟩ : Even ((2 : ℤ) ^ r))
    exact ⟨a + b - 1, by omega⟩
  exact hkill _ hs' _ hodd habs ⟨contract φ D 0, hsum⟩

end SignedDifferenceSets
