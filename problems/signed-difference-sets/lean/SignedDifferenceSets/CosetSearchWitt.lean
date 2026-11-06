module

public import SignedDifferenceSets.CosetSearch
public import SignedDifferenceSets.MultiplierWitt

/-!
# The coset search for every `n` (A7 through I13's C10)

`IsSDS.exists_translate_fixed_contract'` proves C10 for every `n = k − λ ≠ 0`, so `C10Holds`
holds whenever `k ≠ λ` (`c10Holds_of_ne_zero`), and `not_hasSDS_of_cosetRow'` closes a row of
any `n` by `CosetRow` and the coset search.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- C10 for every `n = k − λ ≠ 0` (I13). -/
theorem c10Holds_of_ne_zero {k : ℕ} {lam : ℤ} (hn0 : (k : ℤ) - lam ≠ 0) : C10Holds k lam := by
  intro G H _ _ _ _ _ D φ c hD hφ hc hcop
  exact hD.exists_translate_fixed_contract' φ hφ hc hn0 hcop

/-- A row of any `n`: no SDS when `CosetRow` and the coset search hold. -/
theorem not_hasSDS_of_cosetRow' {ms ds : List ℕ} {c k : ℕ} {lam : ℤ} {t : ℕ} {s : ℤ}
    (h : CosetRow ms ds c k lam t s) (hs : cosetSearch ds c k lam t s = true)
    (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst k lam :=
  not_hasSDS_of_cosetSearch (c10Holds_of_ne_zero h.2.2.1.ne') h hs inst

end SignedDifferenceSets
