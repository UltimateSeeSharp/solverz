module

public import SignedDifferenceSets.MaCheck
public import SignedDifferenceSets.MaLemma
public import SignedDifferenceSets.MaRows.Polys
public import SignedDifferenceSets.SylowTwo

/-!
# C26: Ma's lemma at equality

C21's argument without its last step: on a quotient `ZMod (r p) × K`, the coset sums `Y` satisfy
`p^b ∣ Y(h + u) − Y(h)` for the generator `u = (r, 0)` of the subgroup of order `p`
(`Ma.dvd_contract_sub`). At `p = 2`, `c = 1` (the quotient is `G` itself) and `4 ∣ n`, `D(x)` and
`D(x + u)` are both zero or both nonzero, so `F = Y + Y(· + u)` lies in `{−2, 0, 2}`, and each
term of `Σ (2F − F²) = 4s' − 2k − 2λ` is `0` or `−8` and pairs up under `h ↦ h + u`:
`8 ∣ 2s' − (k + λ)` with
`s' = ±s` (`not_hasSDS_of_maDescent`). This is the parity of the halved SDS `(v/2, (k+λ)/4, λ/2)` on
`G/P`. `DescentCert` checks it on the table's rows.
-/

@[expose] public section

open Polynomial

namespace SignedDifferenceSets

open Ma SylowTrace

/-- C21's divisibility step: `p^b ∣ Y(x + r, k) − Y(x, k)` for the coset sums `Y` on
`ZMod (r p) × K`. -/
theorem Ma.dvd_contract_sub {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K] [Fintype K]
    [DecidableEq K] {p r i e b c k : ℕ} {lam : ℤ} [hp : Fact p.Prime] [NeZero (r * p)]
    {φ : G →+ ZMod (r * p) × K} (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * Fintype.card (ZMod (r * p) × K)) (hr : 0 < r) (hi : 0 < i)
    (hc : ∀ x : K, p ^ i • x = -x) (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam) (hb : 2 * b ≤ e)
    (hcert : CycloFacts p r) {D : G → SignType} (hD : IsSDS k lam D) (x : ZMod (r * p)) (kk : K) :
    (p : ℤ) ^ b ∣ contract φ D (x + (r : ZMod (r * p)), kk) - contract φ D (x, kk) := by
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
  have e1 := coeff_add_of_psiHom_eq_zero hp1 hr hker x kk
  simp only [hEdef, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_smul, Finsupp.coe_sub,
    Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, coeff_ofFun] at e1
  exact ⟨W.coeff (x + (r : ZMod (r * p)), kk) - W.coeff (x, kk), by linear_combination e1⟩

/-- The pair term: for `y, y' ∈ [−1, 1]` with `2 ∣ y' − y`, `16 ∣ 2 (2F − F²)`, `F = y + y'`. -/
theorem dvd_pair_term {y y' : ℤ} (h1 : |y| ≤ 1) (h2 : |y'| ≤ 1) (hd : (2 : ℤ) ∣ y' - y) :
    (16 : ℤ) ∣ 2 * (2 * (y + y') - (y + y') ^ 2) := by
  rw [abs_le] at h1 h2
  obtain ⟨t, ht⟩ := hd
  have hy : y = -1 ∨ y = 0 ∨ y = 1 := by omega
  have hy' : y' = -1 ∨ y' = 0 ∨ y' = 1 := by omega
  rcases hy with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;> first | omega | decide

/-- C26 (parity form): at C21's equality with `p = 2`, `c = 1` and `4 ∣ k − λ`,
`8 ∣ 2s' − (k + λ)` for `s' = ±s`. -/
theorem not_hasSDS_of_maDescent {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K]
    [Fintype K] [DecidableEq K] {r i k : ℕ} {lam : ℤ} [NeZero (r * 2)]
    {φ : G →+ ZMod (r * 2) × K} (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = 1 * Fintype.card (ZMod (r * 2) × K)) (hr : 0 < r) (hi : 0 < i)
    (hc : ∀ x : K, 2 ^ i • x = -x) (hn : (2 : ℤ) ^ 2 ∣ (k : ℤ) - lam) (hcert : CycloFacts 2 r)
    {s : ℤ} (hs : s ^ 2 = k + lam * ((Fintype.card G : ℤ) - 1))
    (hkill : ¬ (8 : ℤ) ∣ 2 * s - (k + lam) ∧ ¬ (8 : ℤ) ∣ -2 * s - (k + lam)) :
    ¬ HasSDS G k lam := by
  intro ⟨D, hD⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := contract φ D with hYdef
  set u : ZMod (r * 2) × K := ((r : ZMod (r * 2)), 0) with hu
  have hrv : ((r : ℕ) : ZMod (r * 2)).val = r :=
    ZMod.val_cast_of_lt (lt_mul_of_one_lt_right hr one_lt_two)
  have hu0 : u ≠ 0 := by
    intro h
    have := congrArg (fun z => (Prod.fst z).val) h
    simp only [hu, Prod.fst_zero, ZMod.val_zero, hrv] at this
    omega
  have huu : u + u = 0 := by
    ext
    · simp only [hu, Prod.fst_add, Prod.fst_zero, ← Nat.cast_add, ← two_mul]
      rw [mul_comm, ZMod.natCast_self]
    · simp [hu]
  have hdiv : ∀ h, (2 : ℤ) ∣ Y (h + u) - Y h := by
    rintro ⟨x, kk⟩
    have := Ma.dvd_contract_sub (b := 1) (e := 2) hφ hcard hr hi hc hn (by norm_num) hcert hD x kk
    simpa [hu] using this
  have hfib := card_fibre_eq hφ hcard
  have hab : ∀ h, |Y h| ≤ 1 := fun h => by
    have := abs_contract_le φ D h
    rw [hfib] at this
    exact_mod_cast this
  have hsq : ∑ h, Y h * Y h = k := by
    have := hD.contract_sq φ
    rw [hfib] at this
    rw [← hYdef] at this
    simpa using this
  have hac : ∑ h, Y h * Y (h + u) = lam := by
    have := hD.contract_autocorr φ u hu0
    rw [hfib] at this
    simpa using this
  have hsum : (∑ h, Y h) ^ 2 = s ^ 2 := by
    rw [hs, hD.sum_contract_sq φ hφ hcard]
    push_cast
    ring
  set q : ZMod (r * 2) × K → ℤ := fun h => 2 * (Y h + Y (h + u)) - (Y h + Y (h + u)) ^ 2 with hq
  have hqsym : ∀ h, q (h + u) = q h := by
    intro h
    simp only [hq, add_assoc, huu, add_zero]
    ring
  have hQ : (16 : ℤ) ∣ ∑ h, q h := by
    have hmem := sum_mem_of_pairs (Ideal.span {(16 : ℤ)}) (· + u)
      (fun h => by simp only [add_assoc, huu, add_zero]) q Finset.univ
      (fun h _ => ⟨Finset.mem_univ _, fun he => hu0 (by simpa using he)⟩)
      (fun h _ => by
        rw [hqsym, ← two_mul, Ideal.mem_span_singleton]
        exact dvd_pair_term (hab h) (hab (h + u)) (hdiv h))
    exact Ideal.mem_span_singleton.1 hmem
  have hshift : ∑ h, Y (h + u) * Y (h + u) = ∑ h, Y h * Y h :=
    Fintype.sum_equiv (Equiv.addRight u) _ _ fun h => rfl
  have hshift1 : ∑ h, Y (h + u) = ∑ h, Y h :=
    Fintype.sum_equiv (Equiv.addRight u) _ _ fun h => rfl
  have hval : ∑ h, q h = 4 * ∑ h, Y h - 2 * k - 2 * lam := by
    simp only [hq, sq, mul_add, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hshift, hshift1, hsq, hac]
    have hcomm : ∑ h, Y (h + u) * Y h = lam := by
      rw [← hac]
      exact Finset.sum_congr rfl fun h _ => mul_comm _ _
    rw [hcomm]
    ring
  rw [hval] at hQ
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsum with h | h
  · exact hkill.1 (by rw [h] at hQ; obtain ⟨t, ht⟩ := hQ; exact ⟨2 * t, by linarith⟩)
  · exact hkill.2 (by rw [h] at hQ; obtain ⟨t, ht⟩ := hQ; exact ⟨2 * t, by linarith⟩)

/-- A C26 certificate: `r = 2^(j−1)`, `i` with `2^i ≡ −1` on `Grp ks`, `s = √(k + λ(v − 1))`,
and the isomorphism onto `ZMod (2r) × Grp ks` as forms `A` with preimages `P`. -/
structure DescentCert where
  r : ℕ
  i : ℕ
  s : ℤ
  ks : List ℕ
  A : List (List ℕ)
  P : List (List ℕ)
  deriving DecidableEq

/-- C26's hypotheses on the row: `c = 1`, `4 ∣ k − λ`, and the parity kill. -/
def DescentCert.Kills (w : Row) (c : DescentCert) : Prop :=
  0 < c.r ∧ 0 < c.i ∧ (∀ m ∈ w.ms, 0 < m) ∧ c.ks ≠ [] ∧ (∀ d ∈ c.ks, d ∣ 2 ^ c.i + 1) ∧
    MapOk w.ms (c.r * 2 :: c.ks) c.A ∧ SurjCert w.ms (c.r * 2 :: c.ks) c.A c.P ∧
    w.ms.prod = c.r * 2 * c.ks.prod ∧ (2 : ℤ) ^ 2 ∣ (w.k : ℤ) - w.lam ∧
    c.s ^ 2 = w.k + w.lam * ((w.ms.prod : ℤ) - 1) ∧
    ¬ (8 : ℤ) ∣ 2 * c.s - (w.k + w.lam) ∧ ¬ (8 : ℤ) ∣ -2 * c.s - (w.k + w.lam) ∧
    (2, c.r) ∈ MaRows.maPairs

instance (w : Row) (c : DescentCert) : Decidable (c.Kills w) := by
  unfold DescentCert.Kills; infer_instance

/-- A row C26 kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem DescentCert.not_hasSDS {w : Row} {c : DescentCert} (h : c.Kills w)
    (inst : Fintype (Grp w.ms)) : ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨hr, hi, -, hne, hks, hmap, hsurj, hprod, hn, hs, hkill1, hkill2, hpair⟩ := h
  obtain ⟨k₀, ks, hks0⟩ := List.exists_cons_of_ne_nil hne
  have : NeZero (c.r * 2) := ⟨(Nat.mul_pos hr two_pos).ne'⟩
  rw [hks0] at hks hmap hsurj hprod
  let _ : Fintype (Grp (k₀ :: ks)) :=
    Grp.fintype _ fun d hd => Nat.pos_of_dvd_of_pos (hks d hd) (by positivity)
  let φ : Grp w.ms →+ ZMod (c.r * 2) × Grp (k₀ :: ks) :=
    linMap w.ms (c.r * 2 :: k₀ :: ks) c.A hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp w.ms) = 1 * Fintype.card (ZMod (c.r * 2) × Grp (k₀ :: ks)) := by
    rw [Fintype.card_prod, ZMod.card, Grp.card_eq, Grp.card_eq, hprod, one_mul]
  have hconj (x : Grp (k₀ :: ks)) : 2 ^ c.i • x = -x := by
    have := Grp.nsmul_eq_zero (N := 2 ^ c.i + 1) (k₀ :: ks) hks x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  refine not_hasSDS_of_maDescent hφ hcard hr hi hconj hn (MaRows.cycloFacts_of_mem_maPairs hpair)
    (s := c.s) ?_ ⟨hkill1, hkill2⟩
  rw [hs, Grp.card_eq]

end SignedDifferenceSets
