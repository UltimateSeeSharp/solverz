module

public import SignedDifferenceSets.CosetSearch
public import SignedDifferenceSets.MultiplierSelfConj

/-!
# The coset search with C25's multipliers (I18)

`CosetRowSelfConj` is `CosetRow` with its condition on `t` relaxed by C25: for each prime
`p ∣ n`, either `t ≡ p^f` on every factor of `ds`, or `p^i ≡ −1` on every factor (`0 < i`) and
`p^(2j) ∥ n`. `not_hasSDS_of_cosetRowSelfConj` closes such a row by the coset search; its proof is
`not_hasSDS_of_cosetSearch`'s with `IsSDS.exists_translate_fixed_contract_selfConj` for C10.
-/

@[expose] public section

namespace SignedDifferenceSets

open CosetSearch OrbitSearch

/-- A row `Grp ms`, `k`, `λ` with quotient `Grp ds` (fibres of size `c`), multiplier `t` and sign
sum `s` meets C25's hypotheses (`n = k − λ > 0` prime to `|H|`; `t` prime to `|H|`; for each
prime `p ∣ n`, `t ≡ p^f` on every factor of `ds`, or `p^i ≡ −1` on every factor with `0 < i`
and `p^(2j) ∥ n`) and C1's (`s² = k + λ (v − 1)`). All by trial division, for `decide +kernel`. -/
def CosetRowSelfConj (ms ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Prop :=
  Dvds ds ms ∧ ms.prod = c * ds.prod ∧ 0 < (k : ℤ) - lam ∧
    Nat.Coprime ds.prod ((k : ℤ) - lam).toNat ∧ Nat.Coprime t ds.prod ∧
    (∀ p ∈ List.range (((k : ℤ) - lam).toNat + 1), ((k : ℤ) - lam).toNat % p = 0 →
      IsPrimeTD p → (∃ f ∈ List.range ds.prod, ∀ d ∈ ds, t % d = p ^ f % d) ∨
        ((∃ i ∈ List.range ds.prod, 0 < i ∧ ∀ d ∈ ds, (p ^ i + 1) % d = 0) ∧
          ∃ j ∈ List.range (((k : ℤ) - lam).toNat + 1),
            ((k : ℤ) - lam).toNat % p ^ (2 * j) = 0 ∧
            ((k : ℤ) - lam).toNat % p ^ (2 * j + 1) ≠ 0)) ∧
    s * s = k + lam * ((ms.prod : ℤ) - 1)

instance (ms ds : List ℕ) (c k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) :
    Decidable (CosetRowSelfConj ms ds c k lam t s) := by
  unfold CosetRowSelfConj; infer_instance

/-- A row meeting `CosetRowSelfConj` whose coset search holds has no SDS: by C25 the coset sums on
`Grp ds` have a translate fixed by `t`, its sum is `±s` (C1), and negating turns `−s` into `s`. -/
theorem not_hasSDS_of_cosetRowSelfConj {ms ds : List ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : CosetRowSelfConj ms ds c k lam t s) (hs : cosetSearch ds c k lam t s = true)
    (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst k lam := by
  rintro ⟨D, hD⟩
  obtain ⟨hdv, hprod, hn, hcop, htH, hpf, hss⟩ := h
  obtain ⟨hds, hchk⟩ := onGrp_spec hs
  let _ : Fintype (Grp ds) := Grp.fintype ds hds
  have hφ := quot_surjective ms ds hdv
  have hcard : Fintype.card (Grp ms) = c * Fintype.card (Grp ds) := by
    rw [Grp.card_eq, Grp.card_eq, hprod]
  have hnz : (k : ℤ) - lam = (((k : ℤ) - lam).toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm
  have hpos : 0 < ((k : ℤ) - lam).toNat := by omega
  have hcopZ : IsCoprime (Fintype.card (Grp ds) : ℤ) ((k : ℤ) - lam) := by
    rw [Grp.card_eq, hnz]
    exact Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨b, hb⟩ := hD.exists_translate_fixed_contract_selfConj (quot ms ds hdv) hφ hcard hn.ne'
    hcopZ
  have hfix := hb t (by rw [Grp.card_eq]; exact htH) fun p hp hpn => by
    have hpn' : p ∣ ((k : ℤ) - lam).toNat := by
      rw [hnz, Int.natCast_dvd_natCast] at hpn
      exact hpn
    rcases hpf p (List.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hpos hpn')))
      (Nat.mod_eq_zero_of_dvd hpn') (isPrimeTD_of_prime hp) with
      ⟨f, -, hf⟩ | ⟨⟨i, -, hi, hdi⟩, j, -, hj, hj1⟩
    · exact Or.inl ⟨f, Grp.nsmul_eq_of_mod ds hf⟩
    · refine Or.inr ⟨⟨i, hi, fun x => ?_⟩, j, ?_, ?_⟩
      · have := Grp.nsmul_eq_zero (N := p ^ i + 1) ds
          (fun d hd => Nat.dvd_of_mod_eq_zero (hdi d hd)) x
        rw [add_smul, one_smul] at this
        exact eq_neg_of_add_eq_zero_left this
      · rw [hnz]
        exact_mod_cast Nat.dvd_of_mod_eq_zero hj
      · rw [hnz]
        intro hd
        exact hj1 (Nat.mod_eq_zero_of_dvd (by exact_mod_cast hd))
  have hfib := card_fibre_eq hφ hcard
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card (Grp ms))
      rw [hcard, h0, zero_mul] at this
      omega
    · exact h0
  set a := contract (quot ms ds hdv) D
  have hdem : Demands c k lam a :=
    { bound := fun h => by
        have := abs_contract_le (quot ms ds hdv) D h
        rwa [hfib] at this
      sq := by rw [hD.contract_sq (quot ms ds hdv), hfib 0, Nat.cast_sub hc1, Nat.cast_one]
      corr := fun g hg => by rw [hD.contract_autocorr (quot ms ds hdv) g hg, hfib]
      abs := hD.sum_abs_contract_le (quot ms ds hdv)
      parity := hD.sum_abs_contract_parity (quot ms ds hdv) }
  have hmm : (k : ℤ) ≤ ∑ h, maxMarked c (a h) := by
    rw [← hD.sum_marked (quot ms ds hdv)]
    refine Finset.sum_le_sum fun h _ => marked_le_maxMarked _ D h ?_
    have := marked_le_card (quot ms ds hdv) D h
    rw [hfib] at this
    exact_mod_cast this
  -- The fixed translate `a'` and its sum `±s`.
  let a' : Grp ds → ℤ := fun h => a (h + b)
  have hda : Demands c k lam a' := hdem.translate b
  have hma : (k : ℤ) ≤ ∑ h, maxMarked c (a' h) := by
    rw [Fintype.sum_equiv (Equiv.addRight b) (fun h => maxMarked c (a' h))
      (fun u => maxMarked c (a u)) fun _ => rfl]
    exact hmm
  have hta : ∀ x, a' (t • x) = a' x := hfix
  have hH1 : 1 ≤ Fintype.card (Grp ds) := Fintype.card_pos
  have hv : ((ms.prod : ℕ) : ℤ) = c * Fintype.card (Grp ds) := by
    rw [Grp.card_eq, hprod, Nat.cast_mul]
  have hsq : (∑ h, a' h) * (∑ h, a' h) = s * s := by
    rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
    simp only [add_zero]
    rw [hda.sq, Finset.sum_congr rfl fun g hg => hda.corr g (Finset.ne_of_mem_erase hg),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hss,
      nsmul_eq_mul, Nat.cast_sub hH1, hv]
    push_cast
    ring
  have key : ∀ a' : Grp ds → ℤ, Demands c k lam a' → (k : ℤ) ≤ ∑ h, maxMarked c (a' h) →
      (∀ x, a' (t • x) = a' x) → ∑ h, a' h = s → False := fun a' h1 h2 h3 h4 =>
    @false_of_cosetCheck (Grp ds) _ _ (Grp.indexed ds hds) _ _ _ _ _ hchk a' h1 h2 h3 h4
  rcases mul_self_eq_mul_self_iff.1 hsq with h1 | h1
  · exact key a' hda hma hta h1
  · have hna : ∀ x, -a' (t • x) = -a' x := fun x => by rw [hta]
    have hns : ∑ h, -a' h = s := by rw [Finset.sum_neg_distrib, h1, neg_neg]
    exact key (fun h => -a' h) hda.neg (by simpa only [maxMarked_neg] using hma) hna hns

end SignedDifferenceSets
