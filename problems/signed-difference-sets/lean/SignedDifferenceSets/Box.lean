module

public import SignedDifferenceSets.Moments

/-!
# The box bound on the coset sums (C14)

On top of C13: the coset sums satisfy `|a_h| ≤ c`, so `a_h = t₀ + q y_h` puts every `y_h` in
`[lo, hi]` with `lo = −⌊(c + t₀)/q⌋`, `hi = ⌊(c − t₀)/q⌋`. Summing `(y − lo)(hi − y) ≥ 0` gives
`S₂ ≤ (lo + hi) S₁ − N lo hi`. A row dies when every `s' = ±s` and `t₀` fails C13's test or
this bound. It reaches every row C6's search over vectors kills beyond C13.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- C13's test and the box bound pass for `N = |H|`, modulus `q`, sign sum `s'`, square sum
`Q`, residue `t₀` and fibre size `c`. -/
def BoxOk (N q s' Q t0 c : ℤ) : Prop :=
  MomentsOk N q s' Q t0 ∧
    (Q - 2 * t0 * s' + N * t0 ^ 2) / q ^ 2 ≤
      (-((c + t0) / q) + (c - t0) / q) * ((s' - N * t0) / q) +
        N * ((c + t0) / q) * ((c - t0) / q)

instance (N q s' Q t0 c : ℤ) : Decidable (BoxOk N q s' Q t0 c) := by
  unfold BoxOk; infer_instance

variable {H : Type*} [AddCommGroup H] [Fintype H]

omit [AddCommGroup H] in
/-- Integer vectors in `[−c, c]`, in one residue class mod `q`, not all equal, pass the box
test. -/
theorem boxOk_of_congr (a : H → ℤ) {q t0 c : ℤ} (hq : 0 < q) (ht : ∀ h, q ∣ a h - t0)
    (hne : ∃ h h', a h ≠ a h') (hc : ∀ h, |a h| ≤ c) :
    BoxOk (Fintype.card H) q (∑ h, a h) (∑ h, a h * a h) t0 c := by
  refine ⟨momentsOk_of_congr a hq ht hne, ?_⟩
  choose y hy using ht
  have ha (h : H) : a h = t0 + q * y h := by linear_combination hy h
  set N : ℤ := (Fintype.card H : ℤ)
  have hS1 : ∑ h, a h - N * t0 = q * ∑ h, y h := by
    have e (h : H) : a h - t0 = q * y h := by rw [ha h]; ring
    rw [Finset.mul_sum, ← Finset.sum_congr rfl fun h _ => e h, Finset.sum_sub_distrib]
    simp [N]
  have hS2 : ∑ h, a h * a h - 2 * t0 * ∑ h, a h + N * t0 ^ 2 = q ^ 2 * ∑ h, y h ^ 2 := by
    have e (h : H) : a h * a h - 2 * t0 * a h + t0 ^ 2 = q ^ 2 * y h ^ 2 := by rw [ha h]; ring
    have hsum := Finset.sum_congr rfl fun h (_ : h ∈ Finset.univ) => e h
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    linear_combination hsum
  have hq0 : q ≠ 0 := hq.ne'
  rw [hS1, Int.mul_ediv_cancel_left _ hq0, hS2, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hq0)]
  set lo := -((c + t0) / q)
  set hi := (c - t0) / q
  have hlo (h : H) : lo ≤ y h := by
    have h1 : -(a h) ≤ c := (abs_le.1 (hc h)).1 |> fun x => by linarith
    have : -(y h) * q ≤ c + t0 := by rw [ha h] at h1; linarith
    have := Int.le_ediv_of_mul_le hq this
    simp only [lo]; linarith
  have hhi (h : H) : y h ≤ hi := by
    have h1 : a h ≤ c := (abs_le.1 (hc h)).2
    have : y h * q ≤ c - t0 := by rw [ha h] at h1; linarith
    exact Int.le_ediv_of_mul_le hq this
  have hpos : 0 ≤ ∑ h, (y h - lo) * (hi - y h) :=
    Finset.sum_nonneg fun h _ => mul_nonneg (by linarith [hlo h]) (by linarith [hhi h])
  have e : ∑ h, (y h - lo) * (hi - y h) =
      (lo + hi) * ∑ h, y h - ∑ h, y h ^ 2 - N * lo * hi := by
    have hsum := Finset.sum_congr rfl fun h (_ : h ∈ Finset.univ) =>
      (show (y h - lo) * (hi - y h) = (lo + hi) * y h - y h ^ 2 - lo * hi by ring)
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hsum
    linear_combination hsum
  have : -lo = (c + t0) / q := by simp [lo]
  rw [e] at hpos
  rw [← this]
  linear_combination hpos

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq H]

omit [DecidableEq H] in
/-- C14: no SDS when, under C5's hypotheses without `2c < p^j`, every sign sum `s' = ±s` and
residue `0 ≤ t₀ < p^j` fails C13's test or the box bound. -/
theorem not_hasSDS_of_box (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) {p i j : ℕ} [Fact p.Prime] (hi : 0 < i)
    (hc : ∀ h : H, p ^ i • h = -h) (hH : (Fintype.card H : ZMod p) ≠ 0) (hH1 : ∃ g : H, g ≠ 0)
    {k : ℕ} {lam : ℤ} (hn : (p : ℤ) ^ (2 * j) ∣ k - lam) (hk : (k : ℤ) ≠ lam) {s : ℤ}
    (hs : s ^ 2 = k + lam * ((c : ℤ) * Fintype.card H - 1))
    (hfail : ∀ s' ∈ [s, -s], ∀ t0 ∈ Finset.Ico (0 : ℤ) ((p : ℤ) ^ j),
      ¬ BoxOk (Fintype.card H) ((p : ℤ) ^ j) s' (k + lam * ((c : ℤ) - 1)) t0 c) :
    ¬ HasSDS G k lam := by
  classical
  rintro ⟨D, hD⟩
  set a := contract φ D
  set q : ℤ := (p : ℤ) ^ j
  have hq : 0 < q := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) j
  have hcong (h : H) : a h ≡ a 0 [ZMOD q] := hD.contract_congr_pow φ hφ hcard hi hc hH hH1 hn h 0
  have ht (h : H) : q ∣ a h - a 0 % q := by
    have := ((hcong h).trans (Int.mod_modEq (a 0) q).symm)
    exact (Int.modEq_iff_dvd.1 this.symm)
  have hb (h : H) : |a h| ≤ c := by
    have := abs_contract_le φ D h
    rwa [card_fibre_eq hφ hcard] at this
  have hok := boxOk_of_congr a hq ht (hD.exists_contract_ne φ hφ hcard hH1 hk) hb
  have hQ : ∑ h, a h * a h = k + lam * ((c : ℤ) - 1) := by
    rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
      Nat.cast_one]
  rw [hQ] at hok
  have hsq := hD.sum_contract_sq φ hφ hcard
  rw [← hs] at hsq
  have hmem : ∑ h, a h ∈ [s, -s] := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact List.mem_cons.2 (Or.inl h)
    · exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 h))
  exact hfail _ hmem _ (Finset.mem_Ico.2 ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩) hok

end SignedDifferenceSets
