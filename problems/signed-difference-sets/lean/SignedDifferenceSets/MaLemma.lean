module

public import SignedDifferenceSets.MaRule
public import SignedDifferenceSets.Multiplier
public import SignedDifferenceSets.SelfConjugacy

/-!
# C21: Ma's lemma on a mixed quotient `ZMod (r p) × K`

The coset sums `Y` of an SDS on `ZMod (r p) × K` map to `A = ℤ[K][X]/(Ψ)`, `Ψ = ∑_{l<p} X^(r l)`
(`psiHom`), where `ψ(Y) σ(ψ(Y)) = n` (`psiHom_mul_conj`; `σ` is `ρ ↦ ρ⁻¹`, `[k] ↦ [−k]`).
`π = ρ − 1` is a non-zero-divisor and `A/πA` is `F_p[K]` (`red`), where C5's Frobenius step
holds; so `y σ(y) ∈ π^N A` puts `y` in `π^M A` for `2M ≤ N` (`exists_pow_mul`). With
`p ~ π^((p−1) r)` (the certificate hypothesis) `ψ(Y) ∈ p^b A`; as `ψ` is onto and its kernel is
periodic along `⟨r⟩` (`coeff_add_of_psiHom_eq_zero`), `Y` is periodic when `2c < p^b`, and then
`p n = 0` in `A`, impossible (`intCast_eq_zero`). `maRule` proves `MaRule`.
-/

@[expose] public section

open Polynomial

namespace SignedDifferenceSets.Ma

/-! ### The ring `A = ℤ[K][X]/(Ψ)`, `Ψ = ∑_{i<p} X^(i r)` -/

variable {K : Type*} [AddCommGroup K]

/-- `Ψ = ∑_{i<p} (X^r)^i`: the cyclotomic polynomial of `p r` when `r = p^(j−1)`. -/
noncomputable def psi (R : Type*) [CommRing R] (p r : ℕ) : R[X] :=
  ∑ i ∈ Finset.range p, (X ^ r) ^ i

theorem psi_mul (R : Type*) [CommRing R] (p r : ℕ) :
    psi R p r * (X ^ r - 1) = X ^ (r * p) - 1 := by
  rw [psi, geom_sum_mul, pow_mul]

theorem psi_monic (R : Type*) [CommRing R] [Nontrivial R] {p r : ℕ} (hp : p ≠ 0) (hr : 0 < r) :
    (psi R p r).Monic :=
  (monic_X_pow r).geom_sum (by rw [natDegree_X_pow]; exact hr) hp

theorem eval_one_psi (R : Type*) [CommRing R] (p r : ℕ) : (psi R p r).eval 1 = p := by
  simp [psi, eval_finsetSum]

/-- The ring `ℤ[K]`. -/
abbrev Rg (K : Type*) [AddCommGroup K] := AddMonoidAlgebra ℤ K

/-- `A = ℤ[K][X]/(Ψ)`. -/
abbrev A (K : Type*) [AddCommGroup K] (p r : ℕ) := AdjoinRoot (psi (Rg K) p r)

theorem natCast_mul_eq_zero {p : ℕ} (hp : p ≠ 0) {w : Rg K} (h : (p : Rg K) * w = 0) :
    w = 0 := by
  rw [← nsmul_eq_mul] at h
  apply AddMonoidAlgebra.coeff_injective
  ext k
  have := congrArg (fun x : Rg K => x.coeff k) h
  simp only [AddMonoidAlgebra.coeff_smul_apply, AddMonoidAlgebra.coeff_zero,
    Finsupp.coe_zero, Pi.zero_apply, smul_eq_zero] at this
  simpa [hp] using this

variable {p r : ℕ}

/-- `ρ ^ (r p) = 1`. -/
theorem root_pow (p r : ℕ) : AdjoinRoot.root (psi (Rg K) p r) ^ (r * p) = 1 := by
  have h := AdjoinRoot.mk_self (f := psi (Rg K) p r)
  have e : AdjoinRoot.mk (psi (Rg K) p r) (X ^ (r * p) - 1) = 0 := by
    rw [← psi_mul, map_mul, h, zero_mul]
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at e
  exact e

/-- `π = ρ − 1` is a non-zero-divisor of `A`. -/
theorem root_sub_one_mul_eq_zero (hp : p ≠ 0) {z : A K p r}
    (h : (AdjoinRoot.root _ - 1) * z = 0) : z = 0 := by
  induction z using AdjoinRoot.induction_on with
  | ih F =>
    have e : (AdjoinRoot.root (psi (Rg K) p r) - 1) * AdjoinRoot.mk _ F =
        AdjoinRoot.mk _ ((X - C 1) * F) := by
      rw [map_mul, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one]
    rw [e, AdjoinRoot.mk_eq_zero] at h
    obtain ⟨W, hW⟩ := h
    have h1 : (W.eval 1) = 0 := by
      have := congrArg (eval 1) hW
      simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, eval_one_psi] at this
      exact natCast_mul_eq_zero hp this.symm
    have hroot : (X - C 1) * (W /ₘ (X - C 1)) = W := mul_divByMonic_eq_iff_isRoot.2 h1
    rw [AdjoinRoot.mk_eq_zero]
    refine ⟨W /ₘ (X - C 1), ?_⟩
    have h2 : (X - C (1 : Rg K)) * (F - psi (Rg K) p r * (W /ₘ (X - C 1))) = 0 := by
      linear_combination hW - psi (Rg K) p r * hroot
    exact sub_eq_zero.1 ((monic_X_sub_C 1).mul_right_eq_zero_iff.1 h2)

/-- Ring homs out of `A` agree when they agree on `ℤ[K]` and on the root. -/
theorem ringHom_ext {S : Type*} [CommRing S] {f g : A K p r →+* S}
    (h1 : ∀ x, f (AdjoinRoot.of _ x) = g (AdjoinRoot.of _ x))
    (h2 : f (AdjoinRoot.root _) = g (AdjoinRoot.root _)) : f = g := by
  refine RingHom.ext fun z => ?_
  induction z using AdjoinRoot.induction_on with
  | ih F =>
    induction F using Polynomial.induction_on' with
    | add F G hF hG => rw [map_add, map_add, map_add, hF, hG]
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X, map_mul, map_mul,
        map_pow, map_pow, h2]
      congr 1
      exact h1 a

/-! ### The group ring `ℤ[ZMod (r p) × K]` maps onto `A` -/

/-- `(a, k) ↦ ρ^a · [k]`. -/
noncomputable def gen (p r : ℕ) [NeZero (r * p)] :
    Multiplicative (ZMod (r * p) × K) →* A K p r where
  toFun h := AdjoinRoot.root _ ^ (Multiplicative.toAdd h).1.val *
    AdjoinRoot.of _ (AddMonoidAlgebra.single (Multiplicative.toAdd h).2 1)
  map_one' := by
    simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero, ZMod.val_zero, pow_zero, one_mul]
    rw [← AddMonoidAlgebra.one_def, map_one]
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    have e : AdjoinRoot.of (psi (Rg K) p r)
        (AddMonoidAlgebra.single ((Multiplicative.toAdd x).2 + (Multiplicative.toAdd y).2) 1) =
        AdjoinRoot.of _ (AddMonoidAlgebra.single (Multiplicative.toAdd x).2 1) *
          AdjoinRoot.of _ (AddMonoidAlgebra.single (Multiplicative.toAdd y).2 1) := by
      rw [← map_mul, AddMonoidAlgebra.single_mul_single, mul_one]
    rw [← pow_eq_pow_mod _ (root_pow p r), pow_add, e]
    ring

/-- `ψ : ℤ[ZMod (r p) × K] → A`. -/
noncomputable def psiHom (p r : ℕ) [NeZero (r * p)] :
    AddMonoidAlgebra ℤ (ZMod (r * p) × K) →ₐ[ℤ] A K p r :=
  AddMonoidAlgebra.lift ℤ (A K p r) (ZMod (r * p) × K) (gen p r)

theorem psiHom_single [NeZero (r * p)] (h : ZMod (r * p) × K) (z : ℤ) :
    psiHom (K := K) p r (AddMonoidAlgebra.single h z) =
      z • (AdjoinRoot.root _ ^ h.1.val * AdjoinRoot.of _ (AddMonoidAlgebra.single h.2 1)) := by
  simp [psiHom, gen]

/-! ### The conjugation `ρ ↦ ρ⁻¹`, `[k] ↦ [−k]` -/

theorem sum_pow_eq_zero_of_mul_eq_one {S : Type*} [CommRing S] {w v : S} (hwv : w * v = 1)
    {n : ℕ} (h : ∑ i ∈ Finset.range n, w ^ i = 0) : ∑ i ∈ Finset.range n, v ^ i = 0 := by
  have e : w ^ (n - 1) * ∑ i ∈ Finset.range n, v ^ i = ∑ i ∈ Finset.range n, w ^ i := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun i => w ^ i) n]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi : i < n := Finset.mem_range.1 hi
    rw [show n - 1 = (n - 1 - i) + i by omega, pow_add, mul_assoc, ← mul_pow, hwv, one_pow,
      mul_one, Nat.add_sub_cancel]
  have e2 : (v * w) ^ (n - 1) = 1 := by rw [mul_comm, hwv, one_pow]
  calc ∑ i ∈ Finset.range n, v ^ i = (v * w) ^ (n - 1) * ∑ i ∈ Finset.range n, v ^ i := by
        rw [e2, one_mul]
    _ = v ^ (n - 1) * (w ^ (n - 1) * ∑ i ∈ Finset.range n, v ^ i) := by rw [mul_pow, mul_assoc]
    _ = 0 := by rw [e, h, mul_zero]

theorem root_mul_conj [NeZero (r * p)] :
    AdjoinRoot.root (psi (Rg K) p r) * AdjoinRoot.root _ ^ (r * p - 1) = 1 := by
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (NeZero.ne _)), root_pow]

theorem eval₂_psi {S : Type*} [CommRing S] (f : Rg K →+* S) (x : S) :
    (psi (Rg K) p r).eval₂ f x = ∑ i ∈ Finset.range p, (x ^ r) ^ i := by
  simp [psi, eval₂_finsetSum, eval₂_pow, eval₂_X]

theorem sum_root_pow : ∑ i ∈ Finset.range p, (AdjoinRoot.root (psi (Rg K) p r) ^ r) ^ i = 0 := by
  have := AdjoinRoot.eval₂_root (psi (Rg K) p r)
  rwa [eval₂_psi] at this

/-- The conjugation of `A`: `ρ ↦ ρ^(r p − 1) = ρ⁻¹`, `[k] ↦ [−k]`. -/
noncomputable def conj (p r : ℕ) [NeZero (r * p)] : A K p r →+* A K p r :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp
      (AddMonoidAlgebra.mapDomainRingHom ℤ (negAddMonoidHom : K →+ K)))
    (AdjoinRoot.root _ ^ (r * p - 1)) (by
      rw [eval₂_psi]
      exact sum_pow_eq_zero_of_mul_eq_one (by rw [← mul_pow, root_mul_conj, one_pow])
        sum_root_pow)

theorem conj_root [NeZero (r * p)] : conj (K := K) p r (AdjoinRoot.root _) = AdjoinRoot.root _ ^ (r
    * p - 1) :=
  AdjoinRoot.lift_root _

theorem conj_of [NeZero (r * p)] (x : Rg K) : conj (K := K) p r (AdjoinRoot.of _ x) =
    AdjoinRoot.of _ (AddMonoidAlgebra.mapDomainRingHom ℤ (negAddMonoidHom : K →+ K) x) :=
  AdjoinRoot.lift_of _

/-- `σ(π) = −ρ⁻¹ π`. -/
theorem conj_root_sub_one [NeZero (r * p)] : conj (K := K) p r (AdjoinRoot.root _ - 1) =
    -AdjoinRoot.root _ ^ (r * p - 1) * (AdjoinRoot.root _ - 1) := by
  rw [map_sub, map_one, conj_root]
  linear_combination root_mul_conj (K := K) (p := p) (r := r)

/-! ### Reduction `A → F_p[K]`, `ρ ↦ 1` -/

/-- `A → F_p[K]`: coefficients mod `p`, `ρ ↦ 1`. -/
noncomputable def red (p r : ℕ) [Fact p.Prime] : A K p r →+* AddMonoidAlgebra (ZMod p) K :=
  AdjoinRoot.lift (AddMonoidAlgebra.mapRingHom K (Int.castRingHom (ZMod p))) 1 (by
    simp [psi, eval₂_finsetSum])

theorem red_root [Fact p.Prime] : red (K := K) p r (AdjoinRoot.root _) = 1 := AdjoinRoot.lift_root _

theorem red_of [Fact p.Prime] (x : Rg K) :
    red (K := K) p r (AdjoinRoot.of _ x) =
      AddMonoidAlgebra.mapRingHom K (Int.castRingHom (ZMod p)) x := AdjoinRoot.lift_of _

/-- `p = π · w` in `A`. -/
theorem natCast_eq (p r : ℕ) : ∃ w : A K p r, (p : A K p r) = (AdjoinRoot.root _ - 1) * w := by
  refine ⟨-AdjoinRoot.mk _ (psi (Rg K) p r /ₘ (X - C 1)), ?_⟩
  have e := modByMonic_add_div (psi (Rg K) p r) (X - C (1 : Rg K))
  rw [modByMonic_X_sub_C_eq_C_eval, eval_one_psi] at e
  have e2 := congrArg (AdjoinRoot.mk (psi (Rg K) p r)) e
  rw [AdjoinRoot.mk_self, map_add, map_mul, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    AdjoinRoot.mk_C, map_one, map_natCast] at e2
  linear_combination e2

/-- Integers vanishing mod `p` in every coefficient are `p` times an element of `ℤ[K]`. -/
theorem exists_eq_natCast_mul {x : Rg K}
    (h : AddMonoidAlgebra.mapRingHom K (Int.castRingHom (ZMod p)) x = 0) :
    ∃ u : Rg K, x = (p : Rg K) * u := by
  have hdvd (k : K) : (p : ℤ) ∣ x.coeff k := by
    have := congrArg (fun y => y.coeff k) h
    simp only [AddMonoidAlgebra.coeff_mapRingHom, eq_intCast, AddMonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  refine ⟨AddMonoidAlgebra.coeffEquiv.symm (x.coeff.mapRange (· / (p : ℤ)) (by simp)), ?_⟩
  rw [← nsmul_eq_mul]
  apply AddMonoidAlgebra.coeff_injective
  ext k
  simp only [AddMonoidAlgebra.coeff_smul_apply]
  change x.coeff k = p • (x.coeff.mapRange (· / (p : ℤ)) (by simp)) k
  rw [Finsupp.mapRange_apply, nsmul_eq_mul, Int.mul_ediv_cancel' (hdvd k)]

/-- The kernel of `red` lies in `π A`. -/
theorem exists_of_red_eq_zero [Fact p.Prime] {z : A K p r} (h : red p r z = 0) :
    ∃ w : A K p r, z = (AdjoinRoot.root _ - 1) * w := by
  induction z using AdjoinRoot.induction_on with
  | ih F =>
    have e := modByMonic_add_div F (X - C (1 : Rg K))
    rw [modByMonic_X_sub_C_eq_C_eval] at e
    rw [red, AdjoinRoot.lift_mk, eval₂_at_one] at h
    obtain ⟨u, hu⟩ := exists_eq_natCast_mul h
    obtain ⟨w, hw⟩ := natCast_eq (K := K) p r
    refine ⟨AdjoinRoot.mk _ (F /ₘ (X - C 1)) + w * AdjoinRoot.of _ u, ?_⟩
    have e2 := congrArg (AdjoinRoot.mk (psi (Rg K) p r)) e
    rw [map_add, map_mul, map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, AdjoinRoot.mk_C, map_one,
      hu, map_mul, map_natCast, hw] at e2
    rw [← e2]
    ring

theorem red_conj [NeZero (r * p)] [Fact p.Prime] (z : A K p r) : red p r (conj p r z) =
    AddMonoidAlgebra.mapDomainRingHom (ZMod p) (negAddMonoidHom : K →+ K) (red p r z) := by
  have := congrArg (fun f : A K p r →+* AddMonoidAlgebra (ZMod p) K => f z)
    (ringHom_ext (f := (red p r).comp (conj p r))
      (g := (AddMonoidAlgebra.mapDomainRingHom (ZMod p) (negAddMonoidHom : K →+ K)).comp
        (red p r)) (fun x => ?_) ?_)
  · exact this
  · simp only [RingHom.comp_apply, conj_of, red_of]
    have e : (AddMonoidAlgebra.mapRingHom K (Int.castRingHom (ZMod p))).comp
        (AddMonoidAlgebra.mapDomainRingHom ℤ (negAddMonoidHom : K →+ K)) =
        (AddMonoidAlgebra.mapDomainRingHom (ZMod p) (negAddMonoidHom : K →+ K)).comp
          (AddMonoidAlgebra.mapRingHom K (Int.castRingHom (ZMod p))) := by
      ext <;> simp
    exact congrArg (fun f => f x) e
  · rw [RingHom.comp_apply, RingHom.comp_apply, conj_root, map_pow, red_root, one_pow, map_one]

/-! ### The Frobenius step (C5 on `K`) -/

theorem eq_zero_of_mul_neg [Fact p.Prime] [Finite K] {i : ℕ} (hi : 0 < i) (hc : ∀ x : K, p ^ i • x =
    -x)
    {y : AddMonoidAlgebra (ZMod p) K}
    (h : y * AddMonoidAlgebra.mapDomainRingHom (ZMod p) (negAddMonoidHom : K →+ K) y = 0) :
    y = 0 := by
  classical
  have := Fintype.ofFinite K
  set b : K → ZMod p := fun k => y.coeff k
  have hy : y = toAlg b := by
    apply AddMonoidAlgebra.coeff_injective
    ext g
    rw [coeff_toAlg]
  have hneg : AddMonoidAlgebra.mapDomainRingHom (ZMod p) (negAddMonoidHom : K →+ K) (toAlg b) =
      toAlg (fun k => b (-k)) := by
    rw [toAlg, map_sum, toAlg]
    simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      negAddMonoidHom_apply]
    exact Fintype.sum_equiv (Equiv.neg K) _ _ (fun k => by simp)
  rw [hy, hneg, toAlg_mul_conj] at h
  have hb : ∀ g, ∑ k, b k * b (k + g) = 0 := by
    intro g
    have := congrArg (fun x : AddMonoidAlgebra (ZMod p) K => x.coeff g) h
    simpa [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] using
      this
  rw [hy, eq_zero_of_autocorr hi hc b hb]
  apply AddMonoidAlgebra.coeff_injective
  ext g
  rw [coeff_toAlg]
  rfl

/-- The key step: `z σ(z) ∈ π A` forces `z ∈ π A`. -/
theorem step [NeZero (r * p)] [Fact p.Prime] [Finite K] {i : ℕ} (hi : 0 < i) (hc : ∀ x : K, p ^ i •
    x = -x) {z w : A K p r}
    (h : z * conj p r z = (AdjoinRoot.root _ - 1) * w) :
    ∃ w' : A K p r, z = (AdjoinRoot.root _ - 1) * w' := by
  apply exists_of_red_eq_zero
  have e := congrArg (red p r) h
  rw [map_mul, map_mul, red_conj, map_sub, red_root, map_one, sub_self, zero_mul] at e
  exact eq_zero_of_mul_neg hi hc e

/-! ### `ψ` and `σ`; the norm identity -/

theorem root_pow_neg [NeZero (r * p)] (a : ZMod (r * p)) :
    (AdjoinRoot.root (psi (Rg K) p r) ^ (r * p - 1)) ^ a.val =
      AdjoinRoot.root _ ^ (-a).val := by
  have h1 : AdjoinRoot.root (psi (Rg K) p r) ^ ((-a).val + a.val) = 1 := by
    rw [pow_eq_pow_mod _ (root_pow p r), ← ZMod.val_add, neg_add_cancel, ZMod.val_zero, pow_zero]
  calc (AdjoinRoot.root (psi (Rg K) p r) ^ (r * p - 1)) ^ a.val
      = AdjoinRoot.root _ ^ ((-a).val + a.val) *
          (AdjoinRoot.root (psi (Rg K) p r) ^ (r * p - 1)) ^ a.val := by rw [h1, one_mul]
    _ = AdjoinRoot.root _ ^ (-a).val *
          (AdjoinRoot.root (psi (Rg K) p r) * AdjoinRoot.root _ ^ (r * p - 1)) ^ a.val := by
        rw [pow_add, mul_pow]; ring
    _ = AdjoinRoot.root _ ^ (-a).val := by rw [root_mul_conj, one_pow, mul_one]

theorem conj_gen [NeZero (r * p)] (h : ZMod (r * p) × K) :
    conj p r (AdjoinRoot.root _ ^ h.1.val * AdjoinRoot.of _ (AddMonoidAlgebra.single h.2 1)) =
      AdjoinRoot.root (psi (Rg K) p r) ^ (-h).1.val *
        AdjoinRoot.of _ (AddMonoidAlgebra.single (-h).2 1) := by
  rw [map_mul, map_pow, conj_root, conj_of, root_pow_neg]
  simp

theorem psiHom_ofFun [NeZero (r * p)] [Fintype K] (Y : ZMod (r * p) × K → ℤ) :
    psiHom p r (ofFun Y) = ∑ h, Y h •
      (AdjoinRoot.root (psi (Rg K) p r) ^ h.1.val *
        AdjoinRoot.of _ (AddMonoidAlgebra.single h.2 1)) := by
  rw [ofFun, map_sum]
  exact Finset.sum_congr rfl fun h _ => psiHom_single h (Y h)

theorem psiHom_neg [NeZero (r * p)] [Fintype K] (Y : ZMod (r * p) × K → ℤ) :
    psiHom p r (ofFun fun h => Y (-h)) = conj p r (psiHom p r (ofFun Y)) := by
  rw [psiHom_ofFun, psiHom_ofFun, map_sum]
  simp only [map_zsmul, conj_gen]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun h => by simp)

theorem univSum_mul_single [NeZero (r * p)] [Fintype K] (g : ZMod (r * p) × K) :
    univSum ℤ (ZMod (r * p) × K) * AddMonoidAlgebra.single g 1 = univSum ℤ _ := by
  rw [univSum, ofFun, Finset.sum_mul]
  simp only [AddMonoidAlgebra.single_mul_single, mul_one]
  exact Fintype.sum_equiv (Equiv.addRight g) _ _ (fun h => rfl)

theorem psiHom_univSum [NeZero (r * p)] [Fintype K] (hp : p ≠ 0) (hrp : 1 < r * p) :
    psiHom (K := K) p r (univSum ℤ _) = 0 := by
  have e := congrArg (psiHom (K := K) p r) (univSum_mul_single ((1 : ZMod (r * p)), (0 : K)))
  rw [map_mul, psiHom_single, one_smul] at e
  have h1 : (1 : ZMod (r * p)).val = 1 := by
    rw [← Nat.cast_one, ZMod.val_natCast, Nat.mod_eq_of_lt hrp]
  rw [h1, pow_one, ← AddMonoidAlgebra.one_def, map_one, mul_one] at e
  apply root_sub_one_mul_eq_zero hp
  linear_combination e

/-- The norm identity: `ψ(Y) σ(ψ(Y)) = n` when `Y`'s autocorrelation is `n [g = 0] + μ`. -/
theorem psiHom_mul_conj [NeZero (r * p)] [Fintype K] [DecidableEq K] (hp : p ≠ 0) (hrp : 1 < r * p)
    {Y : ZMod (r * p) × K → ℤ} {n μ : ℤ}
    (hY : ∀ g, ∑ h, Y h * Y (h + g) = (if g = 0 then n else 0) + μ) :
    psiHom p r (ofFun Y) * conj p r (psiHom p r (ofFun Y)) = n := by
  have e := congrArg (psiHom (K := K) p r) (ofFun_mul_ofFun_neg_of_autocorr (R := ℤ) hY)
  simp only [Int.cast_id] at e
  rw [map_mul, psiHom_neg, map_add, map_mul, psiHom_univSum hp hrp, mul_zero, add_zero,
    map_intCast] at e
  exact e

/-! ### The induction: `y σ(y) ∈ π^N A` puts `y` in `π^M A` for `2M ≤ N` -/

theorem pow_mul_cancel (hp : p ≠ 0) (k : ℕ) {a b : A K p r}
    (h : (AdjoinRoot.root _ - 1) ^ k * a = (AdjoinRoot.root _ - 1) ^ k * b) : a = b := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    rw [← sub_eq_zero]
    apply root_sub_one_mul_eq_zero hp
    rw [pow_succ] at h
    linear_combination h

theorem exists_pow_mul [NeZero (r * p)] [Fact p.Prime] [Finite K] {i : ℕ} (hp : p ≠ 0) (hi : 0 < i)
    (hc : ∀ x : K, p ^ i • x = -x) {y w : A K p r}
    {N : ℕ} (hy : y * conj p r y = (AdjoinRoot.root _ - 1) ^ N * w) :
    ∀ M, 2 * M ≤ N → ∃ z : A K p r, y = (AdjoinRoot.root _ - 1) ^ M * z
  | 0, _ => ⟨y, by rw [pow_zero, one_mul]⟩
  | m + 1, hm => by
    obtain ⟨z, rfl⟩ := exists_pow_mul hp hi hc hy m (by omega)
    set π := AdjoinRoot.root (psi (Rg K) p r) - 1
    set u := AdjoinRoot.root (psi (Rg K) p r) ^ (r * p - 1)
    have hc' : conj p r π = -u * π := conj_root_sub_one
    have hy' := hy
    rw [map_mul, map_pow, hc'] at hy'
    have e1 : π ^ (2 * m) * ((-u) ^ m * (z * conj p r z)) =
        π ^ (2 * m) * (π ^ (N - 2 * m) * w) := by
      calc π ^ (2 * m) * ((-u) ^ m * (z * conj p r z))
          = π ^ m * z * ((-u * π) ^ m * conj p r z) := by ring
        _ = π ^ N * w := hy'
        _ = π ^ (2 * m) * (π ^ (N - 2 * m) * w) := by
          rw [← mul_assoc, ← pow_add, show 2 * m + (N - 2 * m) = N by omega]
    have e2 := pow_mul_cancel hp _ e1
    obtain ⟨d, hd⟩ : ∃ d, N - 2 * m = d + 1 := ⟨N - 2 * m - 1, by omega⟩
    rw [hd] at e2
    have hru : AdjoinRoot.root (psi (Rg K) p r) * u = 1 := root_mul_conj
    have e3 : z * conj p r z =
        π * ((-AdjoinRoot.root (psi (Rg K) p r)) ^ m * π ^ d * w) := by
      have h4 : z * conj p r z = (-AdjoinRoot.root (psi (Rg K) p r)) ^ m * ((-u) ^ m *
          (z * conj p r z)) := by
        rw [← mul_assoc, ← mul_pow, neg_mul_neg, hru, one_pow, one_mul]
      rw [h4, e2, pow_succ]
      ring
    obtain ⟨z', hz'⟩ := step hi hc e3
    exact ⟨z', by rw [hz', pow_succ]; ring⟩

/-! ### Degrees, `ℤ ↪ A`, `ψ` onto -/

theorem natDegree_psi_add (hp : p ≠ 0) (hr : 0 < r) :
    (psi (Rg K) p r).natDegree + r = r * p := by
  have hm := psi_monic (Rg K) hp hr
  have h1 : (X ^ r - 1 : (Rg K)[X]).Monic := by simpa using monic_X_pow_sub_C (1 : Rg K) hr.ne'
  have e := congrArg natDegree (psi_mul (Rg K) p r)
  rw [hm.natDegree_mul h1] at e
  have d1 : (X ^ r - 1 : (Rg K)[X]).natDegree = r := by
    simpa using natDegree_X_pow_sub_C (n := r) (r := (1 : Rg K))
  have d2 : (X ^ (r * p) - 1 : (Rg K)[X]).natDegree = r * p := by
    simpa using natDegree_X_pow_sub_C (n := r * p) (r := (1 : Rg K))
  rw [d1, d2] at e
  exact e

theorem intCast_eq_zero (hp : 1 < p) (hr : 0 < r) {z : ℤ} (h : (z : A K p r) = 0) : z = 0 := by
  by_contra hz
  have e : AdjoinRoot.mk (psi (Rg K) p r) (C (z : Rg K)) = (z : A K p r) := by
    rw [C_eq_intCast, map_intCast]
  rw [← e, AdjoinRoot.mk_eq_zero] at h
  have hz' : C (z : Rg K) ≠ 0 := by
    rw [Ne, C_eq_zero]
    intro h0
    apply hz
    have := congrArg (fun x : Rg K => x.coeff 0) h0
    simpa [AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.coeff_single] using this
  refine (psi_monic (Rg K) (by omega) hr).not_dvd_of_natDegree_lt hz' ?_ h
  have e2 := natDegree_psi_add (K := K) (p := p) (r := r) (by omega) hr
  have : r * 2 ≤ r * p := Nat.mul_le_mul_left r hp
  rw [natDegree_C]
  omega

theorem psiHom_inr [NeZero (r * p)] (x : Rg K) :
    psiHom p r (AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.inr (ZMod (r * p)) K) x) =
      AdjoinRoot.of _ x := by
  have : (psiHom (K := K) p r).toRingHom.comp
      (AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.inr (ZMod (r * p)) K)) =
      AdjoinRoot.of _ := by
    ext <;> simp [psiHom_single]
  exact congrArg (fun f => f x) this

theorem val_one_of_lt (hrp : 1 < r * p) : (1 : ZMod (r * p)).val = 1 := by
  rw [← Nat.cast_one, ZMod.val_natCast, Nat.mod_eq_of_lt hrp]

theorem psiHom_surjective [NeZero (r * p)] (hrp : 1 < r * p) : Function.Surjective (psiHom (K := K)
    p r) := by
  intro a
  induction a using AdjoinRoot.induction_on with
  | ih F =>
    induction F using Polynomial.induction_on' with
    | add F G hF hG =>
      obtain ⟨W1, h1⟩ := hF
      obtain ⟨W2, h2⟩ := hG
      exact ⟨W1 + W2, by rw [map_add, h1, h2, map_add]⟩
    | monomial n x =>
      refine ⟨AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.inr (ZMod (r * p)) K) x *
        AddMonoidAlgebra.single ((1 : ZMod (r * p)), (0 : K)) 1 ^ n, ?_⟩
      rw [map_mul, map_pow, psiHom_single, one_smul, val_one_of_lt hrp, pow_one,
        ← AddMonoidAlgebra.one_def, map_one, mul_one, psiHom_inr, ← C_mul_X_pow_eq_monomial,
        map_mul, map_pow, AdjoinRoot.mk_X]
      rfl

/-! ### The kernel of `ψ`: periodic along `P = ⟨r⟩` -/

/-- `E` as a polynomial over `ℤ[K]`: `∑_(a,k) E(a,k) [k] X^a`. -/
noncomputable def toPoly [NeZero (r * p)] [Fintype K] (E : AddMonoidAlgebra ℤ (ZMod (r * p) × K)) :
    (Rg K)[X] :=
  ∑ h, C (AddMonoidAlgebra.single h.2 (E.coeff h)) * X ^ h.1.val

theorem psiHom_eq_mk [NeZero (r * p)] [Fintype K] (E : AddMonoidAlgebra ℤ (ZMod (r * p) × K)) :
    psiHom p r E = AdjoinRoot.mk _ (toPoly E) := by
  have hE : E = ofFun (fun h => E.coeff h) := by
    apply AddMonoidAlgebra.coeff_injective
    ext g
    rw [coeff_ofFun]
  conv_lhs => rw [hE]
  rw [psiHom_ofFun, toPoly, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.mk_X]
  change E.coeff h • _ = AdjoinRoot.of _ _ * _
  rw [show AddMonoidAlgebra.single h.2 (E.coeff h) = E.coeff h • AddMonoidAlgebra.single h.2 (1 : ℤ)
    by rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one], map_zsmul, smul_mul_assoc]
  exact congrArg (E.coeff h • ·) (mul_comm _ _)

theorem coeff_toPoly [NeZero (r * p)] [Fintype K] (E : AddMonoidAlgebra ℤ (ZMod (r * p) × K)) {a :
    ℕ} (ha : a < r * p) :
    (toPoly E).coeff a = ∑ k, AddMonoidAlgebra.single k (E.coeff ((a : ZMod (r * p)), k)) := by
  rw [toPoly, finsetSum_coeff, Fintype.sum_prod_type]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (a : ZMod (r * p))]
  · simp [ZMod.val_cast_of_lt ha]
  · intro x _ hx
    refine Finset.sum_eq_zero fun k _ => ite_eq_right fun h => hx ?_
    rw [h, ZMod.natCast_zmod_val]
  · simp

theorem coeff_toPoly_of_le [NeZero (r * p)] [Fintype K] (E : AddMonoidAlgebra ℤ (ZMod (r * p) × K))
    {a : ℕ} (ha : r * p ≤ a) :
    (toPoly E).coeff a = 0 := by
  rw [toPoly, finsetSum_coeff]
  refine Finset.sum_eq_zero fun h _ => ?_
  rw [coeff_C_mul_X_pow, ite_eq_right]
  have := ZMod.val_lt h.1
  omega

/-- The kernel of `ψ` is periodic along `P = ⟨r⟩`. -/
theorem coeff_add_of_psiHom_eq_zero [NeZero (r * p)] [Finite K] (hp : 1 < p) (hr : 0 < r)
    {E : AddMonoidAlgebra ℤ (ZMod (r * p) × K)} (hE : psiHom p r E = 0) (x : ZMod (r * p))
    (k : K) : E.coeff (x + (r : ZMod (r * p)), k) = E.coeff (x, k) := by
  have := Fintype.ofFinite K
  rw [psiHom_eq_mk, AdjoinRoot.mk_eq_zero] at hE
  obtain ⟨V, hV⟩ := hE
  set L := toPoly E with hL
  have hm := psi_monic (Rg K) (p := p) (r := r) (by omega) hr
  have hdeg := natDegree_psi_add (K := K) (p := p) (r := r) (by omega) hr
  have hVdeg : ∀ a, r ≤ a → V.coeff a = 0 := by
    by_cases hV0 : V = 0
    · simp [hV0]
    have e1 : L.natDegree = (psi (Rg K) p r).natDegree + V.natDegree := by
      rw [hV, hm.natDegree_mul' hV0]
    have e2 : L.natDegree ≤ r * p - 1 :=
      natDegree_le_iff_coeff_eq_zero.2 fun N hN => coeff_toPoly_of_le E (by omega)
    have : 1 ≤ r * p := by omega
    intro a ha
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hper : ∀ a, r ≤ a → a < r * p → L.coeff a = L.coeff (a - r) := by
    intro a h1 h2
    have e : L * (X ^ r - 1) = V * X ^ (r * p) - V := by
      rw [hV, mul_comm (psi (Rg K) p r) V, mul_assoc, psi_mul]
      ring
    have := congrArg (fun F => F.coeff a) e
    simp only [mul_sub, mul_one, coeff_sub, coeff_mul_X_pow', ite_eq_left h1,
      ite_eq_right (show ¬ r * p ≤ a by omega)] at this
    rw [hVdeg a h1] at this
    linear_combination -this
  have hmod : ∀ a, a < r * p → L.coeff a = L.coeff (a % r) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha
      by_cases h : a < r
      · rw [Nat.mod_eq_of_lt h]
      · rw [hper a (by omega) ha, ih (a - r) (by omega) (by omega)]
        conv_rhs => rw [show a = (a - r) + r by omega, Nat.add_mod_right]
  have hrv : ((r : ℕ) : ZMod (r * p)).val = r :=
    ZMod.val_cast_of_lt (lt_mul_of_one_lt_right hr hp)
  have key : L.coeff (x + (r : ZMod (r * p))).val = L.coeff x.val := by
    rw [hmod _ (ZMod.val_lt _), hmod _ (ZMod.val_lt _), ZMod.val_add, hrv,
      Nat.mod_mod_of_dvd _ (dvd_mul_right r p), Nat.add_mod_right]
  rw [hL, coeff_toPoly E (ZMod.val_lt _), coeff_toPoly E (ZMod.val_lt _), ZMod.natCast_zmod_val,
    ZMod.natCast_zmod_val] at key
  have := congrArg (fun y : Rg K => y.coeff k) key
  classical
  simpa [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.single_apply] using this

end SignedDifferenceSets.Ma

namespace SignedDifferenceSets

open Ma

/-- C21 (Ma's lemma on a mixed quotient). -/
theorem maRule : MaRule := by
  intro G K _ _ _ _ _ p r i e b c k lam hp _ φ hφ hcard hr hi hc hn hk hb hpb hcert ⟨D, hD⟩
  have hp1 : 1 < p := hp.out.one_lt
  have hp0 : p ≠ 0 := by omega
  have hrp : 1 < r * p := lt_of_lt_of_le hp1 (Nat.le_mul_of_pos_left p hr)
  set Y := contract φ D with hYdef
  have hY : ∀ g, ∑ h, Y h * Y (h + g) = (if g = 0 then (k : ℤ) - lam else 0) + lam * c := by
    intro g
    by_cases hg : g = 0
    · subst hg
      simp only [add_zero, ite_true]
      rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
        Nat.cast_one]
      ring
    · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcard, ite_eq_right hg, zero_add]
  set y := psiHom (K := K) p r (ofFun Y) with hydef
  have hnorm : y * conj p r y = (((k : ℤ) - lam : ℤ) : A K p r) := psiHom_mul_conj hp0 hrp hY
  obtain ⟨yc, zc, hpc, hzc⟩ := hcert (A K p r) (AdjoinRoot.root _) sum_root_pow
  obtain ⟨n', hn'⟩ := hn
  have hN : y * conj p r y =
      (AdjoinRoot.root (psi (Rg K) p r) - 1) ^ ((p - 1) * r * e) * (yc ^ e * n') := by
    rw [hnorm, hn', Int.cast_mul, Int.cast_pow, Int.cast_natCast, hpc, mul_pow, ← pow_mul]
    ring
  have hM : 2 * ((p - 1) * r * b) ≤ (p - 1) * r * e := by
    have := Nat.mul_le_mul_left ((p - 1) * r) hb
    nlinarith [this]
  obtain ⟨z, hz⟩ := exists_pow_mul hp0 hi hc hN _ hM
  have hy : y = (p : A K p r) ^ b * (zc ^ b * z) := by
    rw [hz, pow_mul, hzc, mul_pow]
    ring
  obtain ⟨W, hW⟩ := psiHom_surjective (K := K) hrp (zc ^ b * z)
  set E := ofFun Y - ((p : ℤ) ^ b) • W with hEdef
  have hker : psiHom p r E = 0 := by
    rw [hEdef, map_sub, map_zsmul, hW, ← hydef, hy, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast,
      sub_self]
  set g0 : ZMod (r * p) × K := ((r : ZMod (r * p)), 0)
  have hperY : ∀ h, Y (h + g0) = Y h := by
    rintro ⟨x, kk⟩
    have hx : ((x, kk) : ZMod (r * p) × K) + g0 = (x + (r : ZMod (r * p)), kk) := by simp [g0]
    rw [hx]
    have e1 := coeff_add_of_psiHom_eq_zero hp1 hr hker x kk
    simp only [hEdef, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul, Finsupp.coe_sub,
      Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coeff_ofFun] at e1
    have hd : (p : ℤ) ^ b ∣ Y (x + (r : ZMod (r * p)), kk) - Y (x, kk) :=
      ⟨W.coeff (x + (r : ZMod (r * p)), kk) - W.coeff (x, kk), by linear_combination e1⟩
    have hb1 := abs_contract_le φ D (x + (r : ZMod (r * p)), kk)
    have hb2 := abs_contract_le φ D (x, kk)
    rw [card_fibre_eq hφ hcard] at hb1 hb2
    have hlt : |Y (x + (r : ZMod (r * p)), kk) - Y (x, kk)| < (p : ℤ) ^ b := by
      have h3 := abs_sub (Y (x + (r : ZMod (r * p)), kk)) (Y (x, kk))
      have : (2 * c : ℤ) < (p : ℤ) ^ b := by exact_mod_cast hpb
      linarith
    have := Int.eq_zero_of_abs_lt_dvd hd hlt
    linarith
  have hshift : ofFun Y * AddMonoidAlgebra.single g0 1 = ofFun Y := by
    rw [ofFun, Finset.sum_mul]
    simp only [AddMonoidAlgebra.single_mul_single, mul_one]
    exact Fintype.sum_equiv (Equiv.addRight g0) _ _ (fun h => by simp [hperY h])
  have hrv : ((r : ℕ) : ZMod (r * p)).val = r := ZMod.val_cast_of_lt (lt_mul_of_one_lt_right hr hp1)
  have hρ : y * AdjoinRoot.root (psi (Rg K) p r) ^ r = y := by
    have := congrArg (psiHom (K := K) p r) hshift
    rw [map_mul, psiHom_single, one_smul] at this
    simp only [g0, hrv, ← AddMonoidAlgebra.one_def, map_one, mul_one] at this
    exact this
  have hl : ∀ l : ℕ, y * (AdjoinRoot.root (psi (Rg K) p r) ^ r) ^ l = y := by
    intro l
    induction l with
    | zero => rw [pow_zero, mul_one]
    | succ l ih => rw [pow_succ, ← mul_assoc, ih, hρ]
  have hpy : (p : A K p r) * y = 0 := by
    calc (p : A K p r) * y = ∑ l ∈ Finset.range p, y * (AdjoinRoot.root _ ^ r) ^ l := by
          rw [Finset.sum_congr rfl (fun l _ => hl l), Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
      _ = y * ∑ l ∈ Finset.range p, (AdjoinRoot.root _ ^ r) ^ l := by rw [Finset.mul_sum]
      _ = 0 := by rw [sum_root_pow, mul_zero]
  have hzero : (((p : ℤ) * ((k : ℤ) - lam) : ℤ) : A K p r) = 0 := by
    rw [Int.cast_mul, ← hnorm, Int.cast_natCast, ← mul_assoc, hpy, zero_mul]
  rcases mul_eq_zero.1 (intCast_eq_zero hp1 hr hzero) with h | h
  · exact hp0 (by exact_mod_cast h)
  · exact hk (by linarith)

end SignedDifferenceSets
