module

public import SignedDifferenceSets.SelfConjugacy

/-!
# The multiplier theorem for squarefree `n` (C9, C10)

Let `a : G → ℤ` have autocorrelation `n·[g = 0] + μ` (an SDS: `n = k − λ`, `μ = λ`; its coset
sums on a quotient: `μ = λ c`), `n` squarefree and prime to `v = |G|`. If `gcd(t, v) = 1` and,
for every prime `p ∣ n`, `t x = p^f x` on `G` for some `f`, then `t` is a multiplier:
`a x = a (t x − g)` for some `g` (McFarland; Gordon, arXiv:2212.10630, Thm 5.1).

Elementary proof in `ℤ[G]` and `F_p[G]`, with `A = ∑ a x [x]`, `A^(t)` its image under
`x ↦ t x` and `W = A^(t) A^(−1) − μ G`: Frobenius gives `A^(t) = A^(p^f)` mod `p`, so
`W ≡ 0 mod p` for every `p ∣ n` and `W = n U` (`n` squarefree); `W W^(−1) = n²` and `∑ W = n`
force `U = [g]`; then `n A^(t) = W A = n [g] A`. Since `gcd(s, v) = 1` (`s = ∑ a`,
`s² = n + μ v`), the translate of `a` with centroid `∑ a(x) x = 0` is fixed by every such `t`
at once (`g = 0`).
-/

@[expose] public section

open AddMonoidAlgebra

namespace SignedDifferenceSets

section GroupRing

variable {R : Type*} [CommRing R] {G : Type*} [AddCommGroup G] [Fintype G]

/-- `∑ₓ b x · [x]` in `R[G]`. -/
noncomputable def ofFun (b : G → R) : R[G] := ∑ x, single x (b x)

variable (R G) in
/-- The sum of all group elements, `∑ₓ [x]`, in `R[G]`. -/
noncomputable def univSum : R[G] := ofFun fun _ => (1 : R)

omit [AddCommGroup G] in
theorem coeff_ofFun (b : G → R) (g : G) : (ofFun b).coeff g = b g := by
  classical
  simp [ofFun, coeff_sum, coeff_single, Finsupp.single_apply]

omit [AddCommGroup G] in
theorem ofFun_injective : Function.Injective (ofFun : (G → R) → R[G]) := by
  intro b c h
  funext g
  simpa [coeff_ofFun] using congrArg (fun x => x.coeff g) h

theorem ofFun_add (b c : G → R) : ofFun (b + c) = ofFun b + ofFun c := by
  simp [ofFun, single_add, Finset.sum_add_distrib]

theorem ofFun_sub (b c : G → R) : ofFun (b - c) = ofFun b - ofFun c := by
  simp [ofFun, single_sub, Finset.sum_sub_distrib]

omit [AddCommGroup G] in
theorem ofFun_sum {ι : Type*} (s : Finset ι) (f : ι → G → R) :
    ofFun (fun g => ∑ i ∈ s, f i g) = ∑ i ∈ s, ofFun (f i) := by
  refine AddMonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  simp only [coeff_ofFun, coeff_sum, Finsupp.finsetSum_apply]

/-- Multiplying by `r [a]` shifts by `a`. -/
theorem single_mul_ofFun (a : G) (r : R) (b : G → R) :
    single a r * ofFun b = ofFun (fun y => r * b (y - a)) := by
  simp only [ofFun, Finset.mul_sum, single_mul_single]
  exact Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun x => by simp)

theorem intCast_mul_ofFun (z : ℤ) (b : G → R) :
    (z : R[G]) * ofFun b = ofFun (fun y => z * b y) := by
  rw [AddMonoidAlgebra.intCast_def, single_mul_ofFun]
  simp

theorem intCast_eq_ofFun [DecidableEq G] (z : ℤ) :
    (z : R[G]) = ofFun (fun y => if y = 0 then (z : R) else 0) := by
  refine AddMonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  rw [coeff_ofFun, AddMonoidAlgebra.intCast_def, coeff_single, Finsupp.single_apply]
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · simp [hg, hg.symm]

omit [AddCommGroup G] in
theorem ofFun_ite [DecidableEq G] (g : G) :
    ofFun (fun y => if y = g then (1 : R) else 0) = single g 1 := by
  refine AddMonoidAlgebra.ext (Finsupp.ext fun y => ?_)
  rw [coeff_ofFun, coeff_single, Finsupp.single_apply]
  rcases eq_or_ne y g with rfl | hy
  · simp
  · simp [hy, hy.symm]

/-- `b · G = (∑ b) G`. -/
theorem ofFun_mul_univSum (b : G → R) :
    ofFun b * univSum R G = ofFun (fun _ => ∑ x, b x) := by
  calc ofFun b * univSum R G = ∑ x, ofFun (fun _ : G => b x) := by
        rw [ofFun, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by rw [univSum, single_mul_ofFun]; simp
    _ = ofFun (fun _ => ∑ x, b x) := (ofFun_sum Finset.univ fun x (_ : G) => b x).symm

/-- `b · G = s G` for an integer vector with sum `s`. -/
theorem ofFun_intCast_mul_univSum (b : G → ℤ) {s : ℤ} (hs : ∑ x, b x = s) :
    ofFun (fun x => (b x : R)) * univSum R G = (s : R[G]) * univSum R G := by
  rw [ofFun_mul_univSum, univSum, intCast_mul_ofFun, ← hs]
  simp

/-- The product with a conjugate has the cross-correlations as coefficients. -/
theorem ofFun_mul_ofFun_neg (a b : G → R) :
    ofFun a * ofFun (fun h => b (-h)) = ofFun (fun g => ∑ h, a (h + g) * b h) := by
  rw [ofFun_sum]
  change (∑ x, single x (a x)) * (∑ z, single z (b (-z))) =
    ∑ h, ∑ g, single g (a (h + g) * b h)
  rw [Finset.sum_mul_sum]
  simp only [single_mul_single]
  calc ∑ x, ∑ z, single (x + z) (a x * b (-z))
      = ∑ x, ∑ h, single (x - h) (a x * b h) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Fintype.sum_equiv (Equiv.neg G) _ _ (fun z => by simp [sub_eq_add_neg])
    _ = ∑ h, ∑ x, single (x - h) (a x * b h) := Finset.sum_comm
    _ = ∑ h, ∑ g, single g (a (h + g) * b h) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        exact Fintype.sum_equiv (Equiv.subRight h) _ _ (fun x => by simp)

/-- The cross-correlation of two integer vectors, minus `c`, in `R[G]`. -/
theorem ofFun_cross (a b : G → ℤ) (c : ℤ) :
    ofFun (fun g => ((∑ h, a (h + g) * b h - c : ℤ) : R)) =
      ofFun (fun x => (a x : R)) * ofFun (fun x => (b (-x) : R)) -
        (c : R[G]) * univSum R G := by
  rw [ofFun_mul_ofFun_neg (fun x => (a x : R)) (fun x => (b x : R)), univSum, intCast_mul_ofFun,
    ← ofFun_sub]
  congr 1
  funext g
  simp

/-- The group-ring form of an autocorrelation `n·[g = 0] + μ`: `a a^(−1) = n + μ G`. -/
theorem ofFun_mul_ofFun_neg_of_autocorr [DecidableEq G] {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) :
    ofFun (fun x => (a x : R)) * ofFun (fun x => (a (-x) : R)) =
      (n : R[G]) + (μ : R[G]) * univSum R G := by
  rw [ofFun_mul_ofFun_neg (fun x => (a x : R)) (fun x => (a x : R)), univSum, intCast_mul_ofFun,
    intCast_eq_ofFun, ← ofFun_add]
  congr 1
  funext g
  have e := congrArg (Int.cast : ℤ → R) (ha g)
  push_cast at e
  simp only [Pi.add_apply, mul_one]
  exact (Finset.sum_congr rfl fun h _ => mul_comm _ _).trans e

end GroupRing

section Integer

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Multiplication by an integer prime to `|G|` is injective on `G`. -/
theorem zsmul_injective_of_isCoprime {z : ℤ} (hz : IsCoprime z (Fintype.card G : ℤ)) :
    Function.Injective fun x : G => z • x := by
  obtain ⟨u, w, huw⟩ := hz
  have hv (x : G) : (Fintype.card G : ℤ) • x = 0 := by rw [natCast_zsmul, card_nsmul_eq_zero]
  intro x y hxy
  simp only at hxy
  calc x = (u * z + w * Fintype.card G) • x := by rw [huw, one_smul]
    _ = u • (z • x) + w • ((Fintype.card G : ℤ) • x) := by rw [add_smul, mul_smul, mul_smul]
    _ = u • (z • y) + w • ((Fintype.card G : ℤ) • y) := by rw [hxy, hv, hv]
    _ = y := by rw [← mul_smul, ← mul_smul, ← add_smul, huw, one_smul]

omit [AddCommGroup G] in
/-- An integer vector with `∑ u² = 1` and `∑ u = 1` is a point mass. -/
theorem exists_eq_ite_of_sum_sq [DecidableEq G] (u : G → ℤ) (h2 : ∑ y, u y * u y = 1)
    (h1 : ∑ y, u y = 1) : ∃ g, ∀ y, u y = if y = g then 1 else 0 := by
  obtain ⟨g, hg⟩ : ∃ g, u g ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at h2
  refine ⟨g, fun y => ?_⟩
  have hsplit := Finset.add_sum_erase Finset.univ (fun y => u y * u y) (Finset.mem_univ g)
  have hnn : 0 ≤ ∑ y ∈ Finset.univ.erase g, u y * u y :=
    Finset.sum_nonneg fun y _ => mul_self_nonneg _
  have hg1 : 0 + 1 ≤ u g * u g := Int.add_one_le_iff.2 (mul_self_pos.2 hg)
  have hrest : ∑ y ∈ Finset.univ.erase g, u y * u y = 0 := by linarith
  have hzero : ∀ y ∈ Finset.univ.erase g, u y = 0 := fun y hy =>
    mul_self_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun y _ => mul_self_nonneg (u y)).1
      hrest y hy)
  have hsum := Finset.add_sum_erase Finset.univ u (Finset.mem_univ g)
  rw [Finset.sum_eq_zero hzero, add_zero, h1] at hsum
  split_ifs with hy
  · rw [hy, hsum]
  · exact hzero y (Finset.mem_erase.2 ⟨hy, Finset.mem_univ y⟩)

variable [DecidableEq G]

/-- C1 for an autocorrelation `n·[g = 0] + μ`: `(∑ a)² = n + μ v`. -/
theorem sum_sq_of_autocorr {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) :
    (∑ x, a x) ^ 2 = n + μ * Fintype.card G := by
  have hshift (x : G) : ∑ g, a (x + g) = ∑ g, a g :=
    Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
  calc (∑ x, a x) ^ 2 = ∑ x, a x * ∑ g, a (x + g) := by simp only [hshift, ← Finset.sum_mul, sq]
    _ = ∑ g, ∑ x, a x * a (x + g) := by simp only [Finset.mul_sum]; exact Finset.sum_comm
    _ = n + μ * Fintype.card G := by
        rw [Finset.sum_congr rfl fun g _ => ha g]
        simp [Finset.sum_add_distrib]
        ring

/-- The autocorrelation is invariant under automorphisms. -/
theorem autocorr_comp {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) (e : G ≃+ G) (g : G) :
    ∑ h, a (e h) * a (e (h + g)) = (if g = 0 then n else 0) + μ := by
  simp only [map_add]
  rw [Fintype.sum_equiv e.toEquiv (fun h => a (e h) * a (e h + e g))
    (fun h => a h * a (h + e g)) (fun h => rfl), ha]
  simp

/-- The autocorrelation is invariant under translation. -/
theorem autocorr_translate {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) (c g : G) :
    ∑ h, a (h + c) * a (h + g + c) = (if g = 0 then n else 0) + μ := by
  rw [← ha g]
  exact Fintype.sum_equiv (Equiv.addRight c) _ _ (fun h => by simp [add_right_comm])

/-- `x^m t = c^m t` from `x t = c t`. -/
theorem pow_mul_eq_of_mul_eq {A : Type*} [CommRing A] {x c t : A} (h : x * t = c * t) (m : ℕ) :
    x ^ m * t = c ^ m * t := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, pow_succ]; linear_combination x ^ m * h + c * ih

/-- Mod a prime `p ∣ n` (Frobenius): with `σ x = p^f x`, `a^(σ) a^(−1) ≡ μ G`. -/
theorem dvd_cross_of_frobenius {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) {p f : ℕ} (hp : p.Prime)
    (hpn : (p : ℤ) ∣ n) (hpv : ¬ (p : ℤ) ∣ Fintype.card G) (σ : G ≃+ G)
    (hσ : ∀ x, σ x = p ^ f • x) (g : G) :
    (p : ℤ) ∣ ∑ h, a (σ.symm (h + g)) * a h - μ := by
  have : Fact p.Prime := ⟨hp⟩
  have hs2 := sum_sq_of_autocorr ha
  obtain ⟨s, hs⟩ : ∃ s, ∑ x, a x = s := ⟨_, rfl⟩
  rw [hs] at hs2
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = m + 1 :=
    ⟨p ^ f - 1, (Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.pos)).symm⟩
  have hsm : (p : ℤ) ∣ μ * s ^ m - μ := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have hn0 : (n : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).2 hpn
    by_cases hs0 : (s : ZMod p) = 0
    · have hv0 : ((Fintype.card G : ℤ) : ZMod p) ≠ 0 :=
        fun h => hpv ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 h)
      have e := congrArg (Int.cast : ℤ → ZMod p) hs2
      push_cast at e hv0
      have hμ : (μ : ZMod p) * Fintype.card G = 0 := by
        linear_combination -e + (s : ZMod p) * hs0 - hn0
      rw [(mul_eq_zero.1 hμ).resolve_right hv0]
      ring
    · have e : (s : ZMod p) ^ m * s = 1 * s := by
        rw [← pow_succ, ← hm, ZMod.pow_card_pow, one_mul]
      rw [mul_right_cancel₀ hs0 e]
      ring
  have hW := ofFun_cross (R := ZMod p) (fun x => a (σ.symm x)) a μ
  have hY : ofFun (fun x => ((a (σ.symm x) : ℤ) : ZMod p)) =
      ofFun (fun x => ((a x : ℤ) : ZMod p)) ^ (m + 1) := by
    rw [← hm]
    change _ = toAlg (fun x => ((a x : ℤ) : ZMod p)) ^ p ^ f
    rw [toAlg_pow, ofFun]
    simp only [← hσ]
    exact Fintype.sum_equiv σ.symm.toEquiv _ _ (fun y => by simp)
  have hXX := ofFun_mul_ofFun_neg_of_autocorr (R := ZMod p) ha
  have hXT := pow_mul_eq_of_mul_eq (ofFun_intCast_mul_univSum (R := ZMod p) a hs) m
  have hnA : (n : (ZMod p)[G]) = 0 :=
    (CharP.intCast_eq_zero_iff ((ZMod p)[G]) p n).2 hpn
  have hcA : ((μ * s ^ m - μ : ℤ) : (ZMod p)[G]) = 0 :=
    (CharP.intCast_eq_zero_iff ((ZMod p)[G]) p _).2 hsm
  push_cast at hcA
  have hzero : ofFun (fun g => ((∑ h, a (σ.symm (h + g)) * a h - μ : ℤ) : ZMod p)) = 0 := by
    rw [hW, hY]
    linear_combination (ofFun fun x => ((a x : ℤ) : ZMod p)) ^ m * hXX +
      (ofFun fun x => ((a x : ℤ) : ZMod p)) ^ m * hnA +
      (μ : (ZMod p)[G]) * hXT + univSum (ZMod p) G * hcA
  have e := congrArg (fun x => x.coeff g) hzero
  simp only [coeff_ofFun] at e
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 (by simpa using e)

/-- C9 for integer vectors: `t` is a multiplier, `a x = a (t x − g)`. -/
theorem exists_multiplier_of_autocorr {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ)
    (hsq : Squarefree n) (hcop : IsCoprime (Fintype.card G : ℤ) n) {t : ℕ}
    (htv : Nat.Coprime t (Fintype.card G))
    (ht : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ n → ∃ f : ℕ, ∀ x : G, t • x = p ^ f • x) :
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
    rw [← Int.natAbs_dvd_natAbs, ← Nat.prod_primeFactors_of_squarefree
      (Int.squarefree_natAbs.2 hsq)]
    refine Finset.prod_primes_dvd _ (fun q hq => (Nat.prime_of_mem_primeFactors hq).prime)
      fun q hq => ?_
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqn : (q : ℤ) ∣ n := Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactors hq)
    obtain ⟨f, hf⟩ := ht q hqp hqn
    have hqv : ¬ (q : ℤ) ∣ Fintype.card G := fun h => hqp.one_lt.ne' (by
      have := Int.isUnit_iff_natAbs_eq.1 (hcop.isUnit_of_dvd' h hqn)
      simpa using this)
    rw [hw]
    exact Int.natCast_dvd.1
      (dvd_cross_of_frobenius ha hqp hqn hqv σ (fun x => (hσ x).trans (hf x)) g)
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
  have hn0 : n ≠ 0 := hsq.ne_zero
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

/-- C9 with a fixed translate (integer vectors): one translate `x ↦ a (x + c)` is fixed by
every multiplier `t` of `exists_multiplier_of_autocorr` at once. -/
theorem exists_translate_fixed_of_autocorr {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ)
    (hsq : Squarefree n) (hcop : IsCoprime (Fintype.card G : ℤ) n) :
    ∃ c : G, ∀ t : ℕ, Nat.Coprime t (Fintype.card G) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ n → ∃ f : ℕ, ∀ x : G, t • x = p ^ f • x) →
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
  obtain ⟨g, hg⟩ := exists_multiplier_of_autocorr (autocorr_translate ha c) hsq hcop htv ht
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

/-- Signs are determined by their integer values. -/
theorem sign_eq_of_cast_eq {a b : SignType} (h : (a : ℤ) = b) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The autocorrelation of an SDS: `k` at `0`, `λ` elsewhere. -/
theorem IsSDS.autocorr [DecidableEq G] (hD : IsSDS k lam D) (g : G) :
    ∑ h, (D h : ℤ) * (D (h + g) : ℤ) = (if g = 0 then (k : ℤ) - lam else 0) + lam := by
  split_ifs with hg
  · subst hg
    have hself : ∑ x, (D x : ℤ) * D (x + 0) = k := by
      simp only [add_zero]
      rw [← hD.1, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      cases D x <;> simp
    rw [hself]
    ring
  · rw [hD.2 g hg, zero_add]

/-- C9: for an SDS with `n = k − λ` squarefree and prime to `v`, every `t` prime to `v` with
`t x = p^f x` on `G` for each prime `p ∣ n` is a multiplier: `D x = D (t x − g)`. -/
theorem IsSDS.exists_multiplier (hD : IsSDS k lam D) (hsq : Squarefree ((k : ℤ) - lam))
    (hcop : IsCoprime (Fintype.card G : ℤ) ((k : ℤ) - lam)) {t : ℕ}
    (htv : Nat.Coprime t (Fintype.card G))
    (ht : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam → ∃ f : ℕ, ∀ x : G, t • x = p ^ f • x) :
    ∃ g : G, ∀ x, D x = D (t • x - g) := by
  classical
  obtain ⟨g, hg⟩ := exists_multiplier_of_autocorr hD.autocorr hsq hcop htv ht
  exact ⟨g, fun x => sign_eq_of_cast_eq (hg x)⟩

/-- C9 with a fixed translate: some translate `x ↦ D (x + a)` of an SDS with `n = k − λ`
squarefree and prime to `v` is fixed by every such multiplier `t` at once. -/
theorem IsSDS.exists_translate_fixed (hD : IsSDS k lam D) (hsq : Squarefree ((k : ℤ) - lam))
    (hcop : IsCoprime (Fintype.card G : ℤ) ((k : ℤ) - lam)) :
    ∃ a : G, ∀ t : ℕ, Nat.Coprime t (Fintype.card G) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam → ∃ f : ℕ, ∀ x : G, t • x = p ^ f • x) →
        ∀ x, D (t • x + a) = D (x + a) := by
  classical
  obtain ⟨a, ha⟩ := exists_translate_fixed_of_autocorr hD.autocorr hsq hcop
  exact ⟨a, fun t htv ht x => sign_eq_of_cast_eq (ha t htv ht x)⟩

/-- C10: on a quotient `H` (fibres of size `c`) with `|H|` prime to the squarefree `n = k − λ`,
some translate of the coset sums is fixed by every multiplier `t` of `H` at once. -/
theorem IsSDS.exists_translate_fixed_contract {H : Type*} [AddCommGroup H] [Fintype H]
    [DecidableEq H] (hD : IsSDS k lam D) (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) (hsq : Squarefree ((k : ℤ) - lam))
    (hcop : IsCoprime (Fintype.card H : ℤ) ((k : ℤ) - lam)) :
    ∃ b : H, ∀ t : ℕ, Nat.Coprime t (Fintype.card H) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam → ∃ f : ℕ, ∀ x : H, t • x = p ^ f • x) →
        ∀ h, contract φ D (t • h + b) = contract φ D (h + b) := by
  refine exists_translate_fixed_of_autocorr (a := contract φ D) (μ := lam * c) (fun g => ?_)
    hsq hcop
  by_cases hg : g = 0
  · subst hg
    simp only [add_zero, ite_true]
    rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
      Nat.cast_one]
    ring
  · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcard, ite_eq_right hg, zero_add]

end SDS

end SignedDifferenceSets
