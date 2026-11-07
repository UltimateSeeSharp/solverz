module

public import SignedDifferenceSets.MaDescent

/-!
# C26 at `c = 1`: the halved SDS

On `G ≅ ZMod (2r) × K` with `4 ∣ n`, `D(x)` and `D(x + w)` are both zero or both nonzero for the
element `w` of order 2 over `(r, 0)` (`Ma.dvd_contract_sub`), so the coset sums along
`ZMod (2r) × K → ZMod r × K` are `0` or `±2`, and halving them gives an SDS `(v/2, (k + λ)/4, λ/2)`
(`hasSDS_half_of_maDescent`). A row whose halved row has no SDS has none either
(`not_hasSDS_of_half`); the halved row's group is reached by a bijective linear map
(`IsSDS.comp_addEquiv`).
-/

@[expose] public section

namespace SignedDifferenceSets

open Ma

/-- An SDS pulled back along an additive isomorphism is an SDS. -/
theorem IsSDS.comp_addEquiv {H H' : Type*} [AddCommGroup H] [Fintype H] [AddCommGroup H']
    [Fintype H'] {k : ℕ} {lam : ℤ} {D : H → SignType} (hD : IsSDS k lam D) (f : H' ≃+ H) :
    IsSDS k lam (D ∘ f) := by
  refine ⟨?_, fun g hg => ?_⟩
  · rw [← hD.1]
    refine Finset.card_bij (fun x _ => f x) (fun x hx => by simpa using hx)
      (fun a _ b _ h => f.injective h) (fun y hy => ⟨f.symm y, by simpa using hy, by simp⟩)
  · have hfg : f g ≠ 0 := fun h => hg (f.injective (by rw [h, map_zero]))
    rw [← hD.2 (f g) hfg]
    exact Fintype.sum_equiv f.toEquiv _ _ fun x => by simp [map_add]

/-- The coset sums along a composite map add up the coset sums along the first map. -/
theorem contract_comp {G H L : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
    [DecidableEq H] [AddCommGroup L] [DecidableEq L] (φ : G →+ H) (ψ : H →+ L)
    (D : G → SignType) (l : L) :
    contract (ψ.comp φ) D l = ∑ h ∈ Finset.univ.filter (fun h => ψ h = l), contract φ D h := by
  simp only [contract, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => ψ (φ x) = l))
    (t := Finset.univ.filter (fun h => ψ h = l)) (g := φ) (fun x hx => by simpa using hx)]
  refine Finset.sum_congr rfl fun h hh => Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
  constructor
  · exact fun hx => hx.2
  · intro hx
    exact ⟨by rw [hx, hh], hx⟩

/-- C26 at `c = 1`: halving the coset sums along `ZMod (2r) × K → ZMod r × K` gives an SDS
`(v/2, (k + λ)/4, λ/2)`. -/
theorem hasSDS_half_of_maDescent {G K : Type} [AddCommGroup G] [Fintype G] [AddCommGroup K]
    [Fintype K] {r i k k' : ℕ} {lam lam' : ℤ} [NeZero (r * 2)] [NeZero r]
    {φ : G →+ ZMod (r * 2) × K} (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = 1 * Fintype.card (ZMod (r * 2) × K)) (hr : 0 < r) (hi : 0 < i)
    (hc : ∀ x : K, 2 ^ i • x = -x) (hn : (2 : ℤ) ^ 2 ∣ (k : ℤ) - lam) (hcert : CycloFacts 2 r)
    (hk' : 4 * (k' : ℤ) = k + lam) (hl' : 2 * lam' = lam) (h : HasSDS G k lam) :
    HasSDS (ZMod r × K) k' lam' := by
  classical
  obtain ⟨D, hD⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ZMod (r * 2) × K →+ ZMod r × K :=
    ((ZMod.castHom (dvd_mul_right r 2) (ZMod r)).toAddMonoidHom).prodMap (AddMonoidHom.id K)
    with hψdef
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, b⟩
    obtain ⟨a', ha'⟩ := ZMod.ringHom_surjective (ZMod.castHom (dvd_mul_right r 2) (ZMod r)) a
    exact ⟨(a', b), by simp [hψdef, ha']⟩
  set u : ZMod (r * 2) × K := ((r : ZMod (r * 2)), 0) with hu
  have hrv : ((r : ℕ) : ZMod (r * 2)).val = r :=
    ZMod.val_cast_of_lt (lt_mul_of_one_lt_right hr one_lt_two)
  have hu0 : u ≠ 0 := by
    intro h
    have := congrArg (fun z => (Prod.fst z).val) h
    simp only [hu, Prod.fst_zero, ZMod.val_zero, hrv] at this
    omega
  have hψu : ψ u = 0 := by
    simp [hψdef, hu]
  set χ := ψ.comp φ with hχdef
  have hχ : Function.Surjective χ := hψ.comp hφ
  have hcardH : Fintype.card (ZMod (r * 2) × K) = 2 * Fintype.card (ZMod r × K) := by
    rw [Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hcard2 : Fintype.card G = 2 * Fintype.card (ZMod r × K) := by rw [hcard, hcardH, one_mul]
  set Y := contract φ D with hYdef
  set W := contract χ D with hWdef
  -- `W (ψ h) = Y h + Y (h + u)`
  have hfibψ : ∀ h : ZMod (r * 2) × K,
      Finset.univ.filter (fun h' => ψ h' = ψ h) = {h, h + u} := by
    intro h
    symm
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [map_add, hψu]
    · have h2 := card_fibre_eq hψ hcardH (ψ h)
      rw [fibre] at h2
      rw [h2, Finset.card_pair (fun e => hu0 (by simpa using e.symm))]
  have hW : ∀ h, W (ψ h) = Y h + Y (h + u) := by
    intro h
    rw [hWdef, hχdef, contract_comp, hfibψ h,
      Finset.sum_pair (fun e => hu0 (by simpa using e.symm))]
  have hdiv : ∀ h, (2 : ℤ) ∣ Y (h + u) - Y h := by
    rintro ⟨x, kk⟩
    have := Ma.dvd_contract_sub (b := 1) (e := 2) hφ hcard hr hi hc hn (by norm_num) hcert hD x kk
    simpa [hu] using this
  have hWeven : ∀ y, (2 : ℤ) ∣ W y := by
    intro y
    obtain ⟨h, rfl⟩ := hψ y
    obtain ⟨t, ht⟩ := hdiv h
    exact ⟨Y h + t, by rw [hW h]; linarith⟩
  have hWle : ∀ y, |W y| ≤ 2 := by
    intro y
    have := abs_contract_le χ D y
    rwa [card_fibre_eq hχ hcard2, Nat.cast_ofNat] at this
  -- the halved values
  let Z : ZMod r × K → SignType := fun y => if 0 < W y then 1 else if W y < 0 then -1 else 0
  have hZ : ∀ y, 2 * (Z y : ℤ) = W y := by
    intro y
    obtain ⟨t, ht⟩ := hWeven y
    have hb := hWle y
    rw [abs_le] at hb
    have : t = -1 ∨ t = 0 ∨ t = 1 := by omega
    rcases this with rfl | rfl | rfl <;> simp [Z, ht]
  have hsqW := hD.contract_sq χ
  rw [← hWdef, card_fibre_eq hχ hcard2] at hsqW
  refine ⟨Z, ?_, fun g hg => ?_⟩
  · have hsum : ∑ y, (Z y : ℤ) * (Z y : ℤ) = k' := by
      have h4 : 4 * ∑ y, (Z y : ℤ) * (Z y : ℤ) = 4 * (k' : ℤ) := by
        rw [Finset.mul_sum, hk']
        have : ∑ y, 4 * ((Z y : ℤ) * (Z y : ℤ)) = ∑ y, W y * W y :=
          Finset.sum_congr rfl fun y _ => by rw [← hZ y]; ring
        rw [this, hsqW]
        push_cast
        ring
      linarith
    have hcardZ : (((Finset.univ.filter fun y => Z y ≠ 0).card : ℕ) : ℤ) =
        ∑ y, (Z y : ℤ) * (Z y : ℤ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      cases Z y <;> simp
    exact_mod_cast hcardZ.trans hsum
  · have hac := hD.contract_autocorr χ g hg
    rw [← hWdef, card_fibre_eq hχ hcard2] at hac
    have h4 : 4 * ∑ y, (Z y : ℤ) * (Z (y + g) : ℤ) = 4 * lam' := by
      rw [Finset.mul_sum]
      have : ∑ y, 4 * ((Z y : ℤ) * (Z (y + g) : ℤ)) = ∑ y, W y * W (y + g) :=
        Finset.sum_congr rfl fun y _ => by rw [← hZ y, ← hZ (y + g)]; ring
      rw [this, hac]
      push_cast
      linarith
    linarith

/-- A halving certificate: the row's map onto `ZMod (2r) × Grp ks` (forms `A`, preimages `P`,
`c = 1`), the halved row `(ms', k', λ')` and a bijective map `Grp ms' → ZMod r × Grp ks`
(forms `B`, preimages `Q`). -/
structure HalfCert where
  r : ℕ
  i : ℕ
  ks : List ℕ
  A : List (List ℕ)
  P : List (List ℕ)
  ms' : List ℕ
  k' : ℕ
  lam' : ℤ
  B : List (List ℕ)
  Q : List (List ℕ)
  deriving DecidableEq

/-- The halving certificate fits the row. -/
def HalfCert.Ok (w : Row) (c : HalfCert) : Prop :=
  0 < c.r ∧ 0 < c.i ∧ c.ks ≠ [] ∧ (∀ d ∈ c.ks, d ∣ 2 ^ c.i + 1) ∧
    MapOk w.ms (c.r * 2 :: c.ks) c.A ∧ SurjCert w.ms (c.r * 2 :: c.ks) c.A c.P ∧
    w.ms.prod = c.r * 2 * c.ks.prod ∧ (2 : ℤ) ^ 2 ∣ (w.k : ℤ) - w.lam ∧
    4 * (c.k' : ℤ) = w.k + w.lam ∧ 2 * c.lam' = w.lam ∧
    MapOk c.ms' (c.r :: c.ks) c.B ∧ SurjCert c.ms' (c.r :: c.ks) c.B c.Q ∧
    c.ms'.prod = c.r * c.ks.prod ∧ (2, c.r) ∈ MaRows.maPairs

instance (w : Row) (c : HalfCert) : Decidable (c.Ok w) := by
  unfold HalfCert.Ok; infer_instance

/-- C26 at `c = 1`: if the halved row has no SDS, neither has the row. -/
theorem HalfCert.not_hasSDS {w : Row} {c : HalfCert} (h : c.Ok w)
    (inst' : Fintype (Grp c.ms')) (hred : ¬ @HasSDS (Grp c.ms') _ inst' c.k' c.lam')
    (inst : Fintype (Grp w.ms)) : ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  intro hS
  obtain ⟨hr, hi, hne, hks, hmap, hsurj, hprod, hn, hk', hl', hmapB, hsurjB, hprodB, hpair⟩ := h
  obtain ⟨k₀, ks, hks0⟩ := List.exists_cons_of_ne_nil hne
  have : NeZero (c.r * 2) := ⟨(Nat.mul_pos hr two_pos).ne'⟩
  have : NeZero c.r := ⟨hr.ne'⟩
  rw [hks0] at hks hmap hsurj hprod hmapB hsurjB hprodB
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
  obtain ⟨Z, hZ⟩ := hasSDS_half_of_maDescent hφ hcard hr hi hconj hn
    (MaRows.cycloFacts_of_mem_maPairs hpair) hk' hl' hS
  let f : Grp c.ms' →+ ZMod c.r × Grp (k₀ :: ks) := linMap c.ms' (c.r :: k₀ :: ks) c.B hmapB
  have hf : Function.Surjective f := linMap_surjective hmapB hsurjB
  have hfcard : Fintype.card (Grp c.ms') = Fintype.card (ZMod c.r × Grp (k₀ :: ks)) := by
    rw [Grp.card_eq, Fintype.card_prod, ZMod.card, Grp.card_eq, hprodB]
  have hbij : Function.Bijective f := (Fintype.bijective_iff_surjective_and_card f).2 ⟨hf, hfcard⟩
  exact hred ⟨Z ∘ AddEquiv.ofBijective f hbij, hZ.comp_addEquiv _⟩

end SignedDifferenceSets
