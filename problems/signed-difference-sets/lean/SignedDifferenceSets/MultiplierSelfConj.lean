module

public import SignedDifferenceSets.MultiplierWitt
public import SignedDifferenceSets.SelfConjugacy

/-!
# Self-conjugate primes enlarge the coset-sum multipliers (C25)

C10 (`IsSDS.exists_translate_fixed_contract'`) fixes a translate of the coset sums `a` on `H` by
every `t` that is a power of each prime `p ∣ n` on `H`. C25 drops that condition for a prime `p`
self-conjugate on `H` (`p^i x = −x`, `i > 0`) with `p^(2j) ∥ n` (`SelfConjEven`): C5 makes `a`
constant mod `p^j`, so `a = a 0 + p^j z` and `W(g) = ∑ a(σ⁻¹(h + g)) a h − μ` is
`n + p^(2j)·(…)` for every automorphism `σ` (`sq_dvd_cross_of_modEq`). With `pow_dvd_cross` for
the other primes, CRT gives `n ∣ W` (`dvd_cross_selfConj`); the rest is C10's proof
(`exists_multiplier_of_dvd_cross`, a copy of `exists_multiplier_of_autocorr'` from `n ∣ W`).
Credit: Miller, arXiv:2511.10231, Thm 7 (difference sets).
-/

@[expose] public section

open AddMonoidAlgebra

namespace SignedDifferenceSets

/-- `p` is self-conjugate on `H` (`p^i x = −x` for some `i > 0`) and `p^(2j) ∥ n` for some `j`. -/
def SelfConjEven (H : Type*) [AddCommGroup H] (p : ℕ) (n : ℤ) : Prop :=
  (∃ i : ℕ, 0 < i ∧ ∀ x : H, p ^ i • x = -x) ∧
    ∃ j : ℕ, (p : ℤ) ^ (2 * j) ∣ n ∧ ¬ (p : ℤ) ^ (2 * j + 1) ∣ n

/-- CRT over the primes of `n ≠ 0`: `n ∣ z` when for each prime `q ∣ n` some `q^E ∣ z` with
`q^(E+1) ∤ n`. -/
theorem dvd_of_forall_prime_pow_dvd {n z : ℤ} (hn0 : n ≠ 0)
    (h : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ n → ∃ E : ℕ, (q : ℤ) ^ E ∣ z ∧ ¬ (q : ℤ) ^ (E + 1) ∣ n) :
    n ∣ z := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact dvd_zero n
  rw [← Int.natAbs_dvd_natAbs, ← Nat.factorization_prime_le_iff_dvd (Int.natAbs_ne_zero.2 hn0)
    (Int.natAbs_ne_zero.2 hz)]
  intro q hq
  by_cases hqn : q ∣ n.natAbs
  · obtain ⟨E, hE, hE1⟩ := h q hq (Int.natCast_dvd.2 hqn)
    have h1 := Int.natAbs_dvd_natAbs.2 hE
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
    have h2 : n.natAbs.factorization q ≤ E := by
      by_contra hle
      have h3 : q ^ (E + 1) ∣ n.natAbs :=
        (hq.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.2 hn0)).2 (by omega)
      exact hE1 (by exact_mod_cast Int.natCast_dvd.2 h3)
    exact h2.trans ((hq.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.2 hz)).1 h1)
  · rw [Nat.factorization_eq_zero_of_not_dvd hqn]
    exact Nat.zero_le _

section Integer

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The S₂ step: if `a` is constant mod `m` and `m² ∣ n`, then `m² ∣ W(g)` for every
automorphism `σ` and shift `g` (`W(g) = n + m²·(…)`). -/
theorem sq_dvd_cross_of_modEq {a : G → ℤ} {n μ m : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ)
    (hcong : ∀ h, a h ≡ a 0 [ZMOD m]) (hm : m ^ 2 ∣ n) (σ : G ≃+ G) (g : G) :
    m ^ 2 ∣ ∑ h, a (σ.symm (h + g)) * a h - μ := by
  have hz (h : G) : ∃ y, a h - a 0 = m * y := (hcong h).symm.dvd
  choose z hz using hz
  have hsum : ∑ h, z (σ.symm (h + g)) = ∑ h, z h :=
    Fintype.sum_equiv ((Equiv.addRight g).trans σ.symm.toEquiv) _ _ (fun _ => rfl)
  have h0 : ∑ h, a h * a h = n + μ := by simpa using ha 0
  have e (h : G) : a (σ.symm (h + g)) * a h = a h * a h +
      m * a 0 * (z (σ.symm (h + g)) - z h) + m ^ 2 * (z (σ.symm (h + g)) * z h - z h * z h) := by
    linear_combination a h * hz (σ.symm (h + g)) +
      (m * z (σ.symm (h + g)) - a h - m * z h) * hz h
  have e2 : ∑ h, m * a 0 * (z (σ.symm (h + g)) - z h) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum, sub_self, mul_zero]
  have key : ∑ h, a (σ.symm (h + g)) * a h - μ =
      n + m ^ 2 * ∑ h, (z (σ.symm (h + g)) * z h - z h * z h) := by
    rw [Finset.sum_congr rfl fun h _ => e h, Finset.sum_add_distrib, Finset.sum_add_distrib, e2,
      h0, ← Finset.mul_sum]
    ring
  rw [key]
  exact dvd_add hm (dvd_mul_right _ _)

/-- `n ∣ W(g)` for every `n ≠ 0` prime to `v` when `σ` is a power of each prime `q ∣ n` on `G`
or `q` is self-conjugate on `G` with `q^(2j) ∥ n` (C25's divisibility). -/
theorem dvd_cross_selfConj {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) (hn0 : n ≠ 0)
    (hcop : IsCoprime (Fintype.card G : ℤ) n) (σ : G ≃+ G)
    (hσ : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ n →
      (∃ f : ℕ, ∀ x, σ x = q ^ f • x) ∨ SelfConjEven G q n) (g : G) :
    n ∣ ∑ h, a (σ.symm (h + g)) * a h - μ := by
  refine dvd_of_forall_prime_pow_dvd hn0 fun q hq hqn => ?_
  have hqv : ¬ (q : ℤ) ∣ Fintype.card G := fun h => hq.one_lt.ne' (by
    have := Int.isUnit_iff_natAbs_eq.1 (hcop.isUnit_of_dvd' h hqn)
    simpa using this)
  rcases hσ q hq hqn with ⟨f, hf⟩ | ⟨⟨i, hi, hc⟩, j, hj, hj1⟩
  · refine ⟨n.natAbs.factorization q, pow_dvd_cross ha hq ?_ hqv σ hf g, fun h => ?_⟩
    · exact_mod_cast Int.natCast_dvd.2 (Nat.ordProj_dvd n.natAbs q)
    · exact Nat.pow_succ_factorization_not_dvd (Int.natAbs_ne_zero.2 hn0) hq
        (Int.natCast_dvd.1 (by exact_mod_cast h))
  · refine ⟨2 * j, ?_, hj1⟩
    have : Fact q.Prime := ⟨hq⟩
    have hH : (Fintype.card G : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun h => hqv (Int.natCast_dvd_natCast.2 h)
    have hcong (h : G) : a h ≡ a 0 [ZMOD (q : ℤ) ^ j] := by
      by_cases hH1 : ∃ g : G, g ≠ 0
      · exact congr_pow_of_autocorr hi hc hH hH1 j a n μ ha hj h 0
      · push Not at hH1
        have e : h = 0 := hH1 h
        subst e
        exact Int.ModEq.refl _
    have e : ((q : ℤ) ^ j) ^ 2 = (q : ℤ) ^ (2 * j) := by rw [← pow_mul, mul_comm]
    have := sq_dvd_cross_of_modEq ha hcong (by rw [e]; exact hj) σ g
    rwa [e] at this

/-- C10's multiplier step from `n ∣ W`: if `n ∣ W(g)` for every `g`, where
`W(g) = ∑ a(σ⁻¹(h + g)) a h − μ` and `σ x = t x`, then `a x = a (t x − g)` for some `g`. -/
theorem exists_multiplier_of_dvd_cross {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) (hn0 : n ≠ 0) {t : ℕ}
    (htv : Nat.Coprime t (Fintype.card G))
    (hdiv : ∀ σ : G ≃+ G, (∀ x, σ x = t • x) → ∀ g, n ∣ ∑ h, a (σ.symm (h + g)) * a h - μ) :
    ∃ g : G, ∀ x, a x = a (t • x - g) := by
  have hinj : Function.Injective fun x : G => t • x := by
    simpa only [natCast_zsmul] using
      zsmul_injective_of_isCoprime (G := G) (z := t) (Nat.isCoprime_iff_coprime.2 htv)
  let σ : G ≃+ G := AddEquiv.ofBijective (AddMonoidHom.mk' (fun x : G => t • x) (smul_add t))
    (Finite.injective_iff_bijective.1 hinj)
  have hσ (x : G) : σ x = t • x := rfl
  have ha' := autocorr_comp ha σ.symm
  -- `w = a^(t) a^(−1) − μ G` is divisible by `n`
  obtain ⟨w, hw⟩ : ∃ w : G → ℤ, w = fun g => ∑ h, a (σ.symm (h + g)) * a h - μ := ⟨_, rfl⟩
  have hnw (g : G) : n ∣ w g := by
    rw [hw]
    exact hdiv σ hσ g
  have hnw' (g : G) : ∃ c, w g = n * c := hnw g
  choose u hu using hnw'
  -- identities in `ℤ[G]`
  have hs2 := sum_sq_of_autocorr ha
  obtain ⟨s, hs⟩ : ∃ s, ∑ x, a x = s := ⟨_, rfl⟩
  rw [hs] at hs2
  have e2 := ofFun_mul_ofFun_neg_of_autocorr (R := ℤ) ha
  have e1 := ofFun_mul_ofFun_neg_of_autocorr (R := ℤ) ha'
  have e6 := ofFun_intCast_mul_univSum (R := ℤ) a hs
  have e4 := ofFun_intCast_mul_univSum (R := ℤ) (s := s) (fun x => a (-x))
    (by rw [← hs]; exact Fintype.sum_equiv (Equiv.neg G) _ _ fun _ => rfl)
  have e3 := ofFun_intCast_mul_univSum (R := ℤ) (s := s) (fun x => a (σ.symm x))
    (by rw [← hs]; exact Fintype.sum_equiv σ.symm.toEquiv _ _ fun _ => rfl)
  have e5 := ofFun_intCast_mul_univSum (R := ℤ) (s := s) (fun x => a (σ.symm (-x)))
    (by rw [← hs]; exact Fintype.sum_equiv ((Equiv.neg G).trans σ.symm.toEquiv) _ _ fun _ => rfl)
  have e7 := ofFun_intCast_mul_univSum (R := ℤ) (fun _ : G => (1 : ℤ))
    (s := (Fintype.card G : ℤ)) (by simp)
  have e8 : (s : ℤ[G]) ^ 2 = (n : ℤ[G]) + (μ : ℤ[G]) * ((Fintype.card G : ℤ) : ℤ[G]) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℤ[G]) hs2
  have hW := ofFun_cross (R := ℤ) (fun x => a (σ.symm x)) a μ
  have hV := ofFun_cross (R := ℤ) a (fun x => a (σ.symm x)) μ
  simp only [Int.cast_id] at e1 e2 e3 e4 e5 e6 e7 hW hV
  rw [← hw] at hW
  have hwneg : (fun g => ∑ h, a (h + g) * a (σ.symm h) - μ) = fun g => w (-g) := by
    funext g
    rw [hw]
    simp only [sub_left_inj]
    exact Fintype.sum_equiv (Equiv.addRight g) _ _ (fun h => by simp [mul_comm])
  rw [hwneg] at hV
  have e7' : univSum ℤ G * univSum ℤ G =
      ((Fintype.card G : ℤ) : ℤ[G]) * univSum ℤ G := e7
  -- `w w^(−1) = n²` and `w G = n G`
  have hww : ofFun w * ofFun (fun g => w (-g)) = (n : ℤ[G]) ^ 2 := by
    rw [hW, hV]
    linear_combination
      (ofFun a * ofFun fun x => a (-x)) * e1 + ((n : ℤ[G]) + (μ : ℤ[G]) * univSum ℤ G) * e2 -
      (μ : ℤ[G]) * (ofFun fun x => a (-x)) * e3 - (μ : ℤ[G]) * (s : ℤ[G]) * e4 -
      (μ : ℤ[G]) * (ofFun fun x => a (σ.symm (-x))) * e6 - (μ : ℤ[G]) * (s : ℤ[G]) * e5 +
      2 * (μ : ℤ[G]) ^ 2 * e7' - 2 * (μ : ℤ[G]) * univSum ℤ G * e8
  have hwT : ofFun w * univSum ℤ G = (n : ℤ[G]) * univSum ℤ G := by
    rw [hW]
    linear_combination (ofFun fun x => a (σ.symm x)) * e4 + (s : ℤ[G]) * e3 -
      (μ : ℤ[G]) * e7' + univSum ℤ G * e8
  -- coefficient `0`: `∑ w² = n²`, `∑ w = n`
  have hsq2 : ∑ y, w y * w y = n ^ 2 := by
    rw [ofFun_mul_ofFun_neg, ← Int.cast_pow, intCast_eq_ofFun] at hww
    have := congrFun (ofFun_injective hww) 0
    simpa using this
  have hsum : ∑ y, w y = n := by
    rw [ofFun_mul_univSum, univSum, intCast_mul_ofFun] at hwT
    have := congrFun (ofFun_injective hwT) 0
    simpa using this
  have hu2 : ∑ y, u y * u y = 1 := by
    refine mul_left_cancel₀ (pow_ne_zero 2 hn0) ?_
    calc n ^ 2 * ∑ y, u y * u y = ∑ y, w y * w y := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by rw [hu y]; ring
      _ = n ^ 2 * 1 := by rw [hsq2, mul_one]
  have hu1 : ∑ y, u y = 1 := by
    refine mul_left_cancel₀ hn0 ?_
    calc n * ∑ y, u y = ∑ y, w y := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => (hu y).symm
      _ = n * 1 := by rw [hsum, mul_one]
  obtain ⟨g, hg⟩ := exists_eq_ite_of_sum_sq u hu2 hu1
  -- `n a^(t) = w a = n [g] a`
  have hfin : ofFun w * ofFun a = (n : ℤ[G]) * ofFun fun x => a (σ.symm x) := by
    rw [hW]
    linear_combination (ofFun fun x => a (σ.symm x)) * e2 + (μ : ℤ[G]) * e3 - (μ : ℤ[G]) * e6
  have hwg : ofFun w = (n : ℤ[G]) * single g 1 := by
    rw [← ofFun_ite, intCast_mul_ofFun]
    congr 1
    funext y
    rw [hu y, hg y]
    simp
  rw [hwg, mul_assoc, single_mul_ofFun, intCast_mul_ofFun, intCast_mul_ofFun] at hfin
  refine ⟨g, fun x => ?_⟩
  have := congrFun (ofFun_injective hfin) (t • x)
  simp only [Int.cast_id, one_mul] at this
  have hx : σ.symm (t • x) = x := by rw [← hσ, AddEquiv.symm_apply_apply]
  rw [hx] at this
  exact (mul_left_cancel₀ hn0 this).symm

/-- C25 for integer vectors: one translate `x ↦ a (x + c)` is fixed by every `t` prime to `v`
that is a power of each prime `p ∣ n` on `G` not self-conjugate with `p^(2j) ∥ n`. -/
theorem exists_translate_fixed_of_autocorr_selfConj {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ)
    (hn0 : n ≠ 0) (hcop : IsCoprime (Fintype.card G : ℤ) n) :
    ∃ c : G, ∀ t : ℕ, Nat.Coprime t (Fintype.card G) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ n →
        (∃ f : ℕ, ∀ x : G, t • x = p ^ f • x) ∨ SelfConjEven G p n) →
        ∀ x, a (t • x + c) = a (x + c) := by
  have hs2 := sum_sq_of_autocorr ha
  obtain ⟨s, hs⟩ : ∃ s, ∑ x, a x = s := ⟨_, rfl⟩
  rw [hs] at hs2
  have hsv : IsCoprime s (Fintype.card G : ℤ) := by
    rw [← IsCoprime.pow_left_iff (m := 2) two_pos, hs2]
    exact hcop.symm.add_mul_right_left μ
  have hsinj := zsmul_injective_of_isCoprime hsv
  obtain ⟨α, β, hαβ⟩ := hsv
  have hv (y : G) : (Fintype.card G : ℤ) • y = 0 := by rw [natCast_zsmul, card_nsmul_eq_zero]
  refine ⟨α • ∑ x, a x • x, fun t htv ht x => ?_⟩
  set c := α • ∑ x, a x • x with hc
  have hac := autocorr_translate ha c
  obtain ⟨g, hg⟩ := exists_multiplier_of_dvd_cross hac hn0 htv fun σ hσ =>
    dvd_cross_selfConj hac hn0 hcop σ fun q hq hqn =>
      (ht q hq hqn).imp_left fun ⟨f, hf⟩ => ⟨f, fun y => (hσ y).trans (hf y)⟩
  -- the centroid of the translate is `0`
  have hsum : ∑ x, a (x + c) = s := by
    rw [← hs]; exact Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)
  have hcen : ∑ x, a (x + c) • x = 0 := by
    calc ∑ x, a (x + c) • x = ∑ y, a y • (y - c) :=
          Fintype.sum_equiv (Equiv.addRight c) _ _ (fun x => by simp)
      _ = ∑ y, a y • y - s • c := by
          simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs]
      _ = 0 := by
          rw [sub_eq_zero, hc, smul_smul]
          calc ∑ y, a y • y = (α * s + β * Fintype.card G) • ∑ y, a y • y := by
                rw [hαβ, one_smul]
            _ = (s * α) • ∑ y, a y • y := by
                rw [add_smul, mul_smul β, hv, smul_zero, add_zero, mul_comm]
  -- so `g = 0`
  have hbij : Function.Bijective fun x : G => t • x :=
    Finite.injective_iff_bijective.1 (by
      simpa only [natCast_zsmul] using
        zsmul_injective_of_isCoprime (G := G) (z := t) (Nat.isCoprime_iff_coprime.2 htv))
  have hsg : s • g = s • (0 : G) := by
    rw [smul_zero]
    calc s • g = ∑ y, a (y - g + c) • y - ∑ y, a (y + c) • y := by
          rw [hcen, sub_zero]
          calc s • g = ∑ z, a (z + c) • (z + g) := by
                simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, hcen,
                  zero_add]
            _ = ∑ y, a (y - g + c) • y :=
                Fintype.sum_equiv (Equiv.addRight g) _ _ (fun z => by simp)
      _ = ∑ x, a (t • x - g + c) • (t • x) - ∑ y, a (y + c) • y := by
          rw [hbij.sum_comp (fun y => a (y - g + c) • y)]
      _ = t • ∑ x, a (x + c) • x - ∑ y, a (y + c) • y := by
          rw [Finset.smul_sum]
          congr 1
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← hg x, smul_comm]
      _ = 0 := by rw [hcen, smul_zero, sub_zero]
  have hg0 : g = 0 := hsinj hsg
  rw [hg x, hg0, sub_zero]

end Integer

section SDS

variable {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ} {lam : ℤ} {D : G → SignType}

/-- C25: on a quotient `H` (fibres of size `c`) with `|H|` prime to `n = k − λ ≠ 0`, some
translate of the coset sums is fixed by every `t` prime to `|H|` that acts as a power of each
prime `p ∣ n` except those self-conjugate on `H` with `p^(2j) ∥ n`. -/
theorem IsSDS.exists_translate_fixed_contract_selfConj {H : Type*} [AddCommGroup H] [Fintype H]
    [DecidableEq H] (hD : IsSDS k lam D) (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) (hn0 : (k : ℤ) - lam ≠ 0)
    (hcop : IsCoprime (Fintype.card H : ℤ) ((k : ℤ) - lam)) :
    ∃ b : H, ∀ t : ℕ, Nat.Coprime t (Fintype.card H) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam →
        (∃ f : ℕ, ∀ x : H, t • x = p ^ f • x) ∨ SelfConjEven H p ((k : ℤ) - lam)) →
        ∀ h, contract φ D (t • h + b) = contract φ D (h + b) := by
  refine exists_translate_fixed_of_autocorr_selfConj (a := contract φ D) (μ := lam * c)
    (fun g => ?_) hn0 hcop
  by_cases hg : g = 0
  · subst hg
    simp only [add_zero, ite_true]
    rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
      Nat.cast_one]
    ring
  · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcard, ite_eq_right hg, zero_add]

end SDS

end SignedDifferenceSets
