module

public import SignedDifferenceSets.MultiplierWitt
public import SignedDifferenceSets.OrbitSearch

/-!
# The orbit exhaust for every `n` (I5 with I13)

`OrbitRow'` is `OrbitRow` without the squarefree check on `n = k − λ`: C9 for every `n ≠ 0`
(`IsSDS.exists_translate_fixed'`, `MultiplierWitt.lean`) supplies the fixed translate, and
`not_hasSDS_of_orbitRow'` closes the row as `not_hasSDS_of_orbitRow` does. Rows are checked by
`decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- A row `Grp ms`, `k`, `λ` with multiplier `t` and sign sum `s` meets C9's hypotheses for every
`n` (`n = k − λ` positive and prime to `v`; `t` prime to `v` and `≡ p^f` on every factor for each
prime `p ∣ n`) and C1's (`s² = k + λ (v − 1)`), and the orbit exhaust for `s` holds. All by trial
division, for `decide +kernel`. -/
def OrbitRow' (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) : Prop :=
  0 < (k : ℤ) - lam ∧
    Nat.Coprime ms.prod ((k : ℤ) - lam).toNat ∧ Nat.Coprime t ms.prod ∧
    (∀ p ∈ List.range (((k : ℤ) - lam).toNat + 1), ((k : ℤ) - lam).toNat % p = 0 →
      IsPrimeTD p → ∃ f ∈ List.range ms.prod, ∀ m ∈ ms, t % m = p ^ f % m) ∧
    s * s = k + lam * ((ms.prod : ℤ) - 1) ∧ orbitExhaust ms k lam t s = true

instance (ms : List ℕ) (k : ℕ) (lam : ℤ) (t : ℕ) (s : ℤ) :
    Decidable (OrbitRow' ms k lam t s) := by
  unfold OrbitRow'; infer_instance

/-- A row meeting `OrbitRow'` has no SDS: C9 for every `n` gives a translate fixed by `t`, its
sign sum is `±s` (C1), and the negation (C2) turns `−s` into `s`. -/
theorem not_hasSDS_of_orbitRow' {ms : List ℕ} {k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : OrbitRow' ms k lam t s) (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst k lam := by
  rintro ⟨D, hD⟩
  obtain ⟨hn, hcop, htv, hpf, hs, hex⟩ := h
  have hnz : (k : ℤ) - lam = (((k : ℤ) - lam).toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm
  have hpos : 0 < ((k : ℤ) - lam).toNat := by omega
  have hcard : Fintype.card (Grp ms) = ms.prod := Grp.card_eq ms
  have hcopZ : IsCoprime (Fintype.card (Grp ms) : ℤ) ((k : ℤ) - lam) := by
    rw [hcard, hnz]
    exact Nat.isCoprime_iff_coprime.2 hcop
  obtain ⟨a, ha⟩ := hD.exists_translate_fixed' hn.ne' hcopZ
  have hfix := ha t (by rw [hcard]; exact htv) fun p hp hpn => by
    rw [hnz, Int.natCast_dvd_natCast] at hpn
    obtain ⟨f, -, hf⟩ := hpf p (List.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hpos hpn)))
      (Nat.mod_eq_zero_of_dvd hpn) (isPrimeTD_of_prime hp)
    exact ⟨f, Grp.nsmul_eq_of_mod ms hf⟩
  have hD' := hD.translate a
  have hsum := hD'.sum_sq
  rw [hcard] at hsum
  have hss : (∑ x, (D (x + a) : ℤ)) * (∑ x, (D (x + a) : ℤ)) = s * s := by
    rw [← sq, hsum, hs]
  rcases mul_self_eq_mul_self_iff.1 hss with h1 | h1
  · exact orbitExhaust_sound hex inst ⟨_, hD', hfix, h1⟩
  · refine orbitExhaust_sound hex inst ⟨_, hD'.neg, fun x => congrArg Neg.neg (hfix x), ?_⟩
    simp only [SignType.coe_neg, Finset.sum_neg_distrib, h1, neg_neg]

/-! ### Tests -/

-- N1147, (79, 40, 2) in C₇₉ (n = 38 squarefree): `OrbitRow'` accepts what `OrbitRow` accepts.
example : ¬ HasSDS (ZMod 79) 40 2 :=
  not_hasSDS_of_orbitRow' (ms := [79]) (t := 2) (s := 14) (by decide +kernel) _

end SignedDifferenceSets
