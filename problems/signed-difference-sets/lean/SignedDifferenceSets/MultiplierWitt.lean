module

public import SignedDifferenceSets.Multiplier
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# The multiplier theorem for every `n` (C9, C10), through Witt vectors

`Multiplier.lean` proves C9 and C10 for squarefree `n` (C15). The only use of squarefreeness
there is `n ∣ W` for `W = a^(t) a^(−1) − μ G`; `dvd_cross` proves it for every `n ≠ 0` prime to
`v`, so C9 and C10 hold with `n ≠ 0` in place of `Squarefree n` (I13).

For a prime `p ∣ n` let `Λ = 𝕎 k`, the Witt vectors of `k = GaloisField p φ(v)`: a DVR with
uniformizer `p` and a primitive `v`-th root of unity `τ ζ` (Teichmüller lift). Every element of
`Λ` is associated to its image under any ring endomorphism (`associated_map`), and
`Frob^f u = u^(p^f)` on `v`-th roots of unity. So for a character `χ ≠ 1`,
`χ W = Frob^f (χ a) · χ a^(−1)` is associated to `χ a · χ a^(−1) = n`, and `χ W = n` for `χ = 1`.
Fourier inversion gives `n ∣ v W(g)` in `Λ`, hence `p^E ∣ W(g)` in `ℤ` for `p^E ∣ n`
(`pow_dvd_cross`); CRT over the primes of `n` gives `dvd_cross`. The rest is
`exists_multiplier_of_autocorr`'s proof, with `n ≠ 0` for `Squarefree n`.
-/

@[expose] public section

open AddMonoidAlgebra

namespace SignedDifferenceSets

namespace Witt

/-! ### Frobenius and divisibility in `𝕎 k` -/

section WittVector

variable {p : ℕ} [hp : Fact p.Prime] {k : Type*} [Field k]

theorem teichmuller_injective :
    Function.Injective (WittVector.teichmuller p : k →* WittVector p k) := fun r s h => by
  simpa only [WittVector.teichmuller_coeff_zero] using congrArg (fun x => x.coeff 0) h

variable [CharP k p]

/-- `Frob (τ r) = τ (r ^ p)`. -/
theorem frobenius_teichmuller (r : k) :
    WittVector.frobenius (WittVector.teichmuller p r) = WittVector.teichmuller p (r ^ p) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

/-- `p ∣ z` in `𝕎 k` for an integer `z` gives `p ∣ z` in `ℤ` (constant coefficient). -/
theorem prime_dvd_of_dvd_intCast {z : ℤ} (h : (p : WittVector p k) ∣ (z : WittVector p k)) :
    (p : ℤ) ∣ z := by
  obtain ⟨y, hy⟩ := h
  have e := congrArg (WittVector.constantCoeff : WittVector p k →+* k) hy
  rw [map_intCast, map_mul, map_natCast, CharP.cast_eq_zero k p, zero_mul] at e
  exact (CharP.intCast_eq_zero_iff k p z).1 e

/-- `p^E ∣ z` in `𝕎 k` for an integer `z` gives `p^E ∣ z` in `ℤ`. -/
theorem prime_pow_dvd_of_dvd_intCast {z : ℤ} {E : ℕ}
    (h : (p : WittVector p k) ^ E ∣ (z : WittVector p k)) : (p : ℤ) ^ E ∣ z := by
  induction E generalizing z with
  | zero => simp
  | succ E ih =>
    obtain ⟨z', rfl⟩ := ih (dvd_trans (pow_dvd_pow _ E.le_succ) h)
    obtain ⟨y, hy⟩ := h
    have hp0 : (p : WittVector p k) ^ E ≠ 0 := pow_ne_zero _ (WittVector.p_nonzero p k)
    have e : (z' : WittVector p k) = (p : WittVector p k) * y := by
      rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, pow_succ, mul_assoc] at hy
      exact mul_left_cancel₀ hp0 hy
    rw [pow_succ]
    exact mul_dvd_mul_left _ (prime_dvd_of_dvd_intCast ⟨y, e⟩)

/-- `Frob u = u ^ p` for an `m`-th root of unity `u`, given a primitive one in `k`. -/
theorem frobenius_eq_pow {m : ℕ} [NeZero m] {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {u : WittVector p k} (hu : u ^ m = 1) : WittVector.frobenius u = u ^ p := by
  obtain ⟨i, -, rfl⟩ :=
    (hζ.map_of_injective (teichmuller_injective (p := p))).eq_pow_of_pow_eq_one hu
  rw [← map_pow (WittVector.teichmuller p) ζ i, frobenius_teichmuller, map_pow]

/-- `Frob^f u = u ^ p^f` for an `m`-th root of unity `u`, given a primitive one in `k`. -/
theorem frobenius_pow_apply {m : ℕ} [NeZero m] {ζ : k} (hζ : IsPrimitiveRoot ζ m)
    {u : WittVector p k} (hu : u ^ m = 1) (f : ℕ) :
    ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ f) u = u ^ p ^ f := by
  induction f with
  | zero => simp
  | succ f ih =>
    have hu' : (u ^ p ^ f) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]
    rw [RingHom.coe_pow, Function.iterate_succ_apply', ← RingHom.coe_pow, ih,
      frobenius_eq_pow hζ hu', ← pow_mul, ← pow_succ]

variable [PerfectRing k p]

/-- In the DVR `𝕎 k`, `x` and `φ x` are associated for every ring endomorphism `φ`. -/
theorem associated_map (φ : WittVector p k →+* WittVector p k) (x : WittVector p k) :
    Associated (φ x) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' x hx
  rw [map_mul, map_pow, map_natCast]
  exact Associated.mul_left _ ((associated_one_iff_isUnit.2 (b.isUnit.map φ)).trans
    (associated_one_iff_isUnit.2 b.isUnit).symm)

/-- `p^E ∣ Frob x ↔ p^E ∣ x`. -/
theorem pow_dvd_frobenius_iff (E : ℕ) (x : WittVector p k) :
    (p : WittVector p k) ^ E ∣ WittVector.frobenius x ↔ (p : WittVector p k) ^ E ∣ x :=
  (associated_map _ x).dvd_iff_dvd_right

end WittVector

/-- A finite field has a primitive `m`-th root of unity for every `m ∣ q − 1`. -/
theorem exists_isPrimitiveRoot_of_dvd {K : Type*} [Field K] [Finite K] {m : ℕ}
    (hm : m ∣ Nat.card K - 1) : ∃ ζ : K, IsPrimitiveRoot ζ m := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have h1 : IsPrimitiveRoot (g : K) (Nat.card K - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, ← Nat.card_units K, ← hg]
    exact IsPrimitiveRoot.orderOf g
  have hpos : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  obtain ⟨j, hj⟩ := hm
  exact ⟨(g : K) ^ j, h1.pow hpos (by rw [hj, mul_comm])⟩

/-! ### Characters `Multiplicative G →* Rˣ` -/

section Characters

variable {R : Type*} [CommRing R] {G : Type*} [AddCommGroup G]

/-- The value of a character `χ : Multiplicative G →* Rˣ` at `x : G`. -/
def chiVal (χ : Multiplicative G →* Rˣ) (x : G) : R := (χ (Multiplicative.ofAdd x) : R)

theorem chiVal_add (χ : Multiplicative G →* Rˣ) (x y : G) :
    chiVal χ (x + y) = chiVal χ x * chiVal χ y := by
  simp [chiVal]

theorem chiVal_zero (χ : Multiplicative G →* Rˣ) : chiVal χ (0 : G) = 1 := by
  simp [chiVal]

theorem chiVal_nsmul (χ : Multiplicative G →* Rˣ) (m : ℕ) (x : G) :
    chiVal χ (m • x) = chiVal χ x ^ m := by
  simp [chiVal]

theorem chiVal_one (x : G) : chiVal (1 : Multiplicative G →* Rˣ) x = 1 := by
  simp [chiVal]

variable [Fintype G]

theorem chiVal_pow_card (χ : Multiplicative G →* Rˣ) (x : G) :
    chiVal χ x ^ Fintype.card G = 1 := by
  rw [← chiVal_nsmul, card_nsmul_eq_zero, chiVal_zero]

/-- First orthogonality: `∑ₓ χ x = 0` for `χ ≠ 1`. -/
theorem sum_chiVal_eq_zero [IsDomain R] {χ : Multiplicative G →* Rˣ} (hχ : χ ≠ 1) :
    ∑ x, chiVal χ x = 0 := by
  obtain ⟨y, hy⟩ : ∃ y : G, chiVal χ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (MonoidHom.ext fun x => Units.val_eq_one.1 (h (Multiplicative.toAdd x)))
  refine eq_zero_of_mul_eq_self_left hy ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft y) _ _ fun x => (chiVal_add χ y x).symm

variable [HasEnoughRootsOfUnity R (Monoid.exponent (Multiplicative G))]
  [Fintype (Multiplicative G →* Rˣ)]

omit [Fintype G] in
/-- Second orthogonality: `∑_χ χ x = 0` for `x ≠ 0`. -/
theorem sum_dual_chiVal_eq_zero [Finite G] [IsDomain R] {x : G} (hx : x ≠ 0) :
    ∑ χ : Multiplicative G →* Rˣ, chiVal χ x = 0 := by
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Multiplicative G) R
    (a := Multiplicative.ofAdd x) (by simpa using hx)
  have hψ' : chiVal ψ x ≠ 1 := fun h => hψ (Units.val_eq_one.1 h)
  refine eq_zero_of_mul_eq_self_left hψ' ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft ψ) _ _ fun χ => by simp [chiVal]

/-- There are `|G|` characters. -/
theorem card_dual : Fintype.card (Multiplicative G →* Rˣ) = Fintype.card G := by
  rw [Fintype.card_eq_nat_card, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative]

theorem sum_dual_chiVal [IsDomain R] [DecidableEq G] (x : G) :
    ∑ χ : Multiplicative G →* Rˣ, chiVal χ x = if x = 0 then (Fintype.card G : R) else 0 := by
  split_ifs with hx
  · subst hx
    simp [chiVal_zero, card_dual]
  · exact sum_dual_chiVal_eq_zero hx

/-- Fourier inversion: `∑_χ χ(w) χ(−g) = v w(g)`. -/
theorem sum_dual_inversion [IsDomain R] (w : G → R) (g : G) :
    ∑ χ : Multiplicative G →* Rˣ, (∑ y, w y * chiVal χ y) * chiVal χ (-g) =
      (Fintype.card G : R) * w g := by
  classical
  calc ∑ χ : Multiplicative G →* Rˣ, (∑ y, w y * chiVal χ y) * chiVal χ (-g)
      = ∑ y, w y * ∑ χ : Multiplicative G →* Rˣ, chiVal χ (y - g) := by
        simp only [Finset.sum_mul, Finset.mul_sum, sub_eq_add_neg, chiVal_add, mul_assoc]
        exact Finset.sum_comm
    _ = (Fintype.card G : R) * w g := by
        simp only [sum_dual_chiVal, sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
        ring

end Characters

/-! ### Characters on the group ring -/

section GroupRing

variable {R : Type*} [CommRing R] {G : Type*} [AddCommGroup G]

/-- A character as an algebra map `R[G] → R`. -/
noncomputable def chiAlg (χ : Multiplicative G →* Rˣ) : R[G] →ₐ[R] R :=
  AddMonoidAlgebra.lift R R G ((Units.coeHom R).comp χ)

theorem chiAlg_single (χ : Multiplicative G →* Rˣ) (x : G) (r : R) :
    chiAlg χ (single x r) = r * chiVal χ x := by
  simp [chiAlg, chiVal, smul_eq_mul]

variable [Fintype G]

theorem chiAlg_ofFun (χ : Multiplicative G →* Rˣ) (b : G → R) :
    chiAlg χ (ofFun b) = ∑ x, b x * chiVal χ x := by
  simp only [ofFun, map_sum, chiAlg_single]

theorem chiAlg_univSum (χ : Multiplicative G →* Rˣ) :
    chiAlg χ (univSum R G) = ∑ x, chiVal χ x := by
  simp only [univSum, chiAlg_ofFun, one_mul]

end GroupRing

/-! ### The local step: `p^E ∣ W(g)` -/

section Local

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] {p : ℕ} [hp : Fact p.Prime]
  {k : Type*} [Field k] [CharP k p] [PerfectRing k p]

/-- The local step in `𝕎 k`, `k` perfect with a primitive `v`-th root of unity: `p^E ∣ n`
gives `p^E ∣ W(g)` for `W = a^(t) a^(−1) − μ`, `t x = p^f x`. -/
theorem pow_dvd_cross_of_witt {ζ : k} (hζ : IsPrimitiveRoot ζ (Fintype.card G)) {a : G → ℤ}
    {n μ : ℤ} (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) {E f : ℕ}
    (hpE : (p : ℤ) ^ E ∣ n) (hpv : ¬ (p : ℤ) ∣ Fintype.card G) (σ : G ≃+ G)
    (hσ : ∀ x, σ x = p ^ f • x) (g : G) :
    (p : ℤ) ^ E ∣ ∑ h, a (σ.symm (h + g)) * a h - μ := by
  have hτ : IsPrimitiveRoot (WittVector.teichmuller p ζ) (Fintype.card G) :=
    hζ.map_of_injective teichmuller_injective
  have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  have : HasEnoughRootsOfUnity (WittVector p k) (Fintype.card G) :=
    ⟨⟨_, hτ⟩, rootsOfUnity.isCyclic _ _⟩
  have : HasEnoughRootsOfUnity (WittVector p k) (Monoid.exponent (Multiplicative G)) :=
    HasEnoughRootsOfUnity.of_dvd _
      (by simpa using Group.exponent_dvd_card (G := Multiplicative G))
  have : Fintype (Multiplicative G →* (WittVector p k)ˣ) := Fintype.ofFinite _
  -- every character value of `W` is divisible by `n`
  have hchar (χ : Multiplicative G →* (WittVector p k)ˣ) :
      (n : WittVector p k) ∣
        ∑ y, ((∑ h, a (σ.symm (h + y)) * a h - μ : ℤ) : WittVector p k) * chiVal χ y := by
    have e1 := congrArg (chiAlg χ)
      (ofFun_cross (R := WittVector p k) (fun x => a (σ.symm x)) a μ)
    have e2 := congrArg (chiAlg χ) (ofFun_mul_ofFun_neg_of_autocorr (R := WittVector p k) ha)
    simp only [map_sub, map_mul, map_intCast, chiAlg_ofFun, chiAlg_univSum] at e1
    simp only [map_mul, map_add, map_intCast, chiAlg_ofFun, chiAlg_univSum] at e2
    have hterm (y : G) : ((a (σ.symm y) : ℤ) : WittVector p k) * chiVal χ y =
        ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ f)
          (((a (σ.symm y) : ℤ) : WittVector p k) * chiVal χ (σ.symm y)) := by
      rw [map_mul, map_intCast, frobenius_pow_apply hζ (chiVal_pow_card χ _) f, ← chiVal_nsmul,
        ← hσ, AddEquiv.apply_symm_apply]
    have hfrob : ∑ x, ((a (σ.symm x) : ℤ) : WittVector p k) * chiVal χ x =
        ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ f)
          (∑ x, ((a x : ℤ) : WittVector p k) * chiVal χ x) := by
      rw [map_sum]
      exact Fintype.sum_equiv σ.symm.toEquiv _ _ hterm
    rw [hfrob] at e1
    rw [e1]
    by_cases hχ : χ = 1
    · subst hχ
      have hfix : ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ f)
          (∑ x, ((a x : ℤ) : WittVector p k) * chiVal 1 x) =
          ∑ x, ((a x : ℤ) : WittVector p k) * chiVal 1 x := by
        simp only [chiVal_one, mul_one]
        rw [← Int.cast_sum, map_intCast]
      rw [hfix, e2, add_sub_cancel_right]
    · rw [sum_chiVal_eq_zero hχ, mul_zero, sub_zero]
      rw [sum_chiVal_eq_zero hχ, mul_zero, add_zero] at e2
      rw [← e2]
      exact ((associated_map _ _).mul_right _).symm.dvd
  -- Fourier inversion: `n ∣ v W(g)` in `𝕎 k`
  have hinv := sum_dual_inversion (R := WittVector p k)
    (fun y => ((∑ h, a (σ.symm (h + y)) * a h - μ : ℤ) : WittVector p k)) g
  have hdiv : (n : WittVector p k) ∣
      (((Fintype.card G : ℤ) * (∑ h, a (σ.symm (h + g)) * a h - μ) : ℤ) : WittVector p k) := by
    rw [Int.cast_mul, Int.cast_natCast, ← hinv]
    exact Finset.dvd_sum fun χ _ => (hchar χ).mul_right _
  have hpow : (p : WittVector p k) ^ E ∣
      (((Fintype.card G : ℤ) * (∑ h, a (σ.symm (h + g)) * a h - μ) : ℤ) : WittVector p k) := by
    refine dvd_trans ?_ hdiv
    obtain ⟨c, hc⟩ := hpE
    exact ⟨c, by rw [hc]; push_cast; ring⟩
  have hcop : IsCoprime ((p : ℤ) ^ E) (Fintype.card G : ℤ) :=
    ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp.out)).2 hpv).pow_left
  exact hcop.dvd_of_dvd_mul_left (prime_pow_dvd_of_dvd_intCast hpow)

end Local

end Witt

section Integer

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The local step with `k = GaloisField q φ(v)`: `q^E ∣ n` gives `q^E ∣ W(g)` for a prime
`q ∤ v` and `t x = q^f x`. -/
theorem pow_dvd_cross {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) {q E f : ℕ}
    (hq : q.Prime) (hqE : (q : ℤ) ^ E ∣ n) (hqv : ¬ (q : ℤ) ∣ Fintype.card G) (σ : G ≃+ G)
    (hσ : ∀ x, σ x = q ^ f • x) (g : G) :
    (q : ℤ) ^ E ∣ ∑ h, a (σ.symm (h + g)) * a h - μ := by
  have : Fact q.Prime := ⟨hq⟩
  have hcop : Nat.Coprime q (Fintype.card G) :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hqv (Int.natCast_dvd_natCast.2 h)
  have hF : Nat.totient (Fintype.card G) ≠ 0 := (Nat.totient_pos.2 Fintype.card_pos).ne'
  have hdvd : Fintype.card G ∣ Nat.card (GaloisField q (Nat.totient (Fintype.card G))) - 1 := by
    rw [GaloisField.card q _ hF]
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hq.pos)).1 (Nat.ModEq.pow_totient hcop).symm
  obtain ⟨ζ, hζ⟩ := Witt.exists_isPrimitiveRoot_of_dvd hdvd
  exact Witt.pow_dvd_cross_of_witt (k := GaloisField q (Nat.totient (Fintype.card G))) hζ ha
    hqE hqv σ hσ g

/-- `n ∣ W(g)` for every `n ≠ 0` prime to `v` (CRT over the primes of `n`): the step of
`exists_multiplier_of_autocorr` that needs `n` squarefree there. -/
theorem dvd_cross {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) (hn0 : n ≠ 0)
    (hcop : IsCoprime (Fintype.card G : ℤ) n) (σ : G ≃+ G)
    (hσ : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ n → ∃ f : ℕ, ∀ x, σ x = q ^ f • x) (g : G) :
    n ∣ ∑ h, a (σ.symm (h + g)) * a h - μ := by
  rcases eq_or_ne (∑ h, a (σ.symm (h + g)) * a h - μ) 0 with hz | hz
  · rw [hz]
    exact dvd_zero n
  rw [← Int.natAbs_dvd_natAbs, ← Nat.factorization_prime_le_iff_dvd (Int.natAbs_ne_zero.2 hn0)
    (Int.natAbs_ne_zero.2 hz)]
  intro q hq
  by_cases hqn : q ∣ n.natAbs
  · have hqn' : (q : ℤ) ∣ n := Int.natCast_dvd.2 hqn
    obtain ⟨f, hf⟩ := hσ q hq hqn'
    have hqv : ¬ (q : ℤ) ∣ Fintype.card G := fun h => hq.one_lt.ne' (by
      have := Int.isUnit_iff_natAbs_eq.1 (hcop.isUnit_of_dvd' h hqn')
      simpa using this)
    have hE : (q : ℤ) ^ (n.natAbs.factorization q) ∣ n := by
      exact_mod_cast Int.natCast_dvd.2 (Nat.ordProj_dvd n.natAbs q)
    have h := Int.natAbs_dvd_natAbs.2 (pow_dvd_cross ha hq hE hqv σ hf g)
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h
    exact (hq.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.2 hz)).1 h
  · rw [Nat.factorization_eq_zero_of_not_dvd hqn]
    exact Nat.zero_le _

/-- C9 for integer vectors and every `n ≠ 0` prime to `v`: `t` is a multiplier,
`a x = a (t x − g)`. -/
theorem exists_multiplier_of_autocorr' {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ)
    (hn0 : n ≠ 0) (hcop : IsCoprime (Fintype.card G : ℤ) n) {t : ℕ}
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
    rw [hw]
    exact dvd_cross ha hn0 hcop σ (fun q hq hqn => (ht q hq hqn).imp fun f hf x =>
      (hσ x).trans (hf x)) g
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

/-- C9 with a fixed translate (integer vectors): one translate `x ↦ a (x + c)` is fixed by
every multiplier `t` of `exists_multiplier_of_autocorr'` at once. -/
theorem exists_translate_fixed_of_autocorr' {a : G → ℤ} {n μ : ℤ}
    (ha : ∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ)
    (hn0 : n ≠ 0) (hcop : IsCoprime (Fintype.card G : ℤ) n) :
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
  obtain ⟨g, hg⟩ := exists_multiplier_of_autocorr' (autocorr_translate ha c) hn0 hcop htv ht
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

/-- C9 for every `n`: for an SDS with `n = k − λ ≠ 0` prime to `v`, every `t` prime to `v` with
`t x = p^f x` on `G` for each prime `p ∣ n` is a multiplier: `D x = D (t x − g)`. -/
theorem IsSDS.exists_multiplier' (hD : IsSDS k lam D) (hn0 : (k : ℤ) - lam ≠ 0)
    (hcop : IsCoprime (Fintype.card G : ℤ) ((k : ℤ) - lam)) {t : ℕ}
    (htv : Nat.Coprime t (Fintype.card G))
    (ht : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam → ∃ f : ℕ, ∀ x : G, t • x = p ^ f • x) :
    ∃ g : G, ∀ x, D x = D (t • x - g) := by
  classical
  obtain ⟨g, hg⟩ := exists_multiplier_of_autocorr' hD.autocorr hn0 hcop htv ht
  exact ⟨g, fun x => sign_eq_of_cast_eq (hg x)⟩

/-- C9 with a fixed translate: some translate `x ↦ D (x + a)` of an SDS with `n = k − λ ≠ 0`
prime to `v` is fixed by every such multiplier `t` at once. -/
theorem IsSDS.exists_translate_fixed' (hD : IsSDS k lam D) (hn0 : (k : ℤ) - lam ≠ 0)
    (hcop : IsCoprime (Fintype.card G : ℤ) ((k : ℤ) - lam)) :
    ∃ a : G, ∀ t : ℕ, Nat.Coprime t (Fintype.card G) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam → ∃ f : ℕ, ∀ x : G, t • x = p ^ f • x) →
        ∀ x, D (t • x + a) = D (x + a) := by
  classical
  obtain ⟨a, ha⟩ := exists_translate_fixed_of_autocorr' hD.autocorr hn0 hcop
  exact ⟨a, fun t htv ht x => sign_eq_of_cast_eq (ha t htv ht x)⟩

/-- C10: on a quotient `H` (fibres of size `c`) with `|H|` prime to `n = k − λ ≠ 0`,
some translate of the coset sums is fixed by every multiplier `t` of `H` at once. -/
theorem IsSDS.exists_translate_fixed_contract' {H : Type*} [AddCommGroup H] [Fintype H]
    [DecidableEq H] (hD : IsSDS k lam D) (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) (hn0 : (k : ℤ) - lam ≠ 0)
    (hcop : IsCoprime (Fintype.card H : ℤ) ((k : ℤ) - lam)) :
    ∃ b : H, ∀ t : ℕ, Nat.Coprime t (Fintype.card H) →
      (∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam → ∃ f : ℕ, ∀ x : H, t • x = p ^ f • x) →
        ∀ h, contract φ D (t • h + b) = contract φ D (h + b) := by
  refine exists_translate_fixed_of_autocorr' (a := contract φ D) (μ := lam * c) (fun g => ?_)
    hn0 hcop
  by_cases hg : g = 0
  · subst hg
    simp only [add_zero, ite_true]
    rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
      Nat.cast_one]
    ring
  · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcard, ite_eq_right hg, zero_add]

end SDS

end SignedDifferenceSets
