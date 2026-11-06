module

public import SignedDifferenceSets.SelfConjugacy

/-!
# Residue class and moments of the coset sums (C6, arithmetic part)

Under C5's hypotheses the coset sums `a` on `H` (`N = |H|`) agree mod `q = p^j`, so
`a_h = t₀ + q y_h` with `0 ≤ t₀ < q`. Their sum is the sign sum `s'` with
`s'² = k + λ(v − 1)`, and their squares add up to `Q = k + λ(c − 1)` (C3). Hence
`S₁ = Σ y = (s' − N t₀)/q` and `S₂ = Σ y² = (Q − 2 t₀ s' + N t₀²)/q²` are integers, and
`z = y − m` (any `m`) has `Σ z² ≥ Σ z`, `Σ z² ≡ Σ z (mod 2)` and `Σ z² ≠ 0`, since the
coset sums are not all equal. A row dies when every `s' = ±s` and `t₀` fails this.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- The moments test passes for `N = |H|`, modulus `q`, sign sum `s'`, square sum `Q` and
residue `t₀`, with `m = S₁ / N`. -/
def MomentsOk (N q s' Q t0 : ℤ) : Prop :=
  q ∣ s' - N * t0 ∧ q ^ 2 ∣ Q - 2 * t0 * s' + N * t0 ^ 2 ∧
    let S1 := (s' - N * t0) / q
    let S2 := (Q - 2 * t0 * s' + N * t0 ^ 2) / q ^ 2
    let m := S1 / N
    (S2 - S1) % 2 = 0 ∧ S1 - N * m ≤ S2 - 2 * m * S1 + N * m ^ 2 ∧
      S2 - 2 * m * S1 + N * m ^ 2 ≠ 0

instance (N q s' Q t0 : ℤ) : Decidable (MomentsOk N q s' Q t0) := by
  unfold MomentsOk; infer_instance

variable {H : Type*} [AddCommGroup H] [Fintype H]

omit [AddCommGroup H] in
/-- Integer vectors in one residue class mod `q`, not all equal, pass the moments test. -/
theorem momentsOk_of_congr (a : H → ℤ) {q t0 : ℤ} (hq : 0 < q) (ht : ∀ h, q ∣ a h - t0)
    (hne : ∃ h h', a h ≠ a h') :
    MomentsOk (Fintype.card H) q (∑ h, a h) (∑ h, a h * a h) t0 := by
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
  have e1 : (∑ h, a h - N * t0) / q = ∑ h, y h := by
    rw [hS1, Int.mul_ediv_cancel_left _ hq0]
  have e2 : (∑ h, a h * a h - 2 * t0 * ∑ h, a h + N * t0 ^ 2) / q ^ 2 = ∑ h, y h ^ 2 := by
    rw [hS2, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 hq0)]
  refine ⟨⟨_, hS1⟩, ⟨_, hS2⟩, ?_⟩
  simp only [e1, e2]
  set m := (∑ h, y h) / N
  have hz : ∑ h, (y h - m) ^ 2 = ∑ h, y h ^ 2 - 2 * m * ∑ h, y h + N * m ^ 2 := by
    have hsum := Finset.sum_congr rfl fun h (_ : h ∈ Finset.univ) =>
      (show (y h - m) ^ 2 = y h ^ 2 - 2 * m * y h + m ^ 2 by ring)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    linear_combination hsum
  have hz1 : ∑ h, (y h - m) = ∑ h, y h - N * m := by
    simp [Finset.sum_sub_distrib, N]
  refine ⟨?_, ?_, ?_⟩
  · have hev : ∀ h, Even ((y h) ^ 2 - y h) := fun h => by
      have := Int.even_mul_pred_self (y h)
      convert this using 1; ring
    have := Finset.even_sum (s := Finset.univ) (f := fun h => y h ^ 2 - y h) fun h _ => hev h
    rw [Finset.sum_sub_distrib] at this
    exact Int.even_iff.1 this
  · rw [← hz, ← hz1]
    exact Finset.sum_le_sum fun h _ => by nlinarith [sq_nonneg (y h - m - 1)]
  · rw [← hz]
    intro h0
    have hall : ∀ h, y h = m := fun h => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun h _ => sq_nonneg (y h - m))).1 h0 h
        (Finset.mem_univ _)
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
    obtain ⟨h, h', hh⟩ := hne
    exact hh (by rw [ha, ha h', hall, hall])

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq H]

/-- With `k ≠ λ` and `H` nontrivial, the coset sums of an SDS are not all equal. -/
theorem IsSDS.exists_contract_ne {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) (hH1 : ∃ g : H, g ≠ 0) (hk : (k : ℤ) ≠ lam) :
    ∃ h h', contract φ D h ≠ contract φ D h' := by
  by_contra hall
  push Not at hall
  obtain ⟨g, hg⟩ := hH1
  have e1 := hD.contract_autocorr φ g hg
  have e2 := hD.contract_sq φ
  rw [Finset.sum_congr rfl fun h _ => by rw [hall h 0, hall (h + g) 0]] at e1
  rw [Finset.sum_congr rfl fun h _ => by rw [hall h 0]] at e2
  rw [card_fibre_eq hφ hcard] at e1 e2
  rw [Nat.cast_sub (one_le_of_card hcard), Nat.cast_one] at e2
  apply hk
  linear_combination e1 - e2

/-- C1 through the coset sums: their sum squared is `k + λ(v − 1)`. -/
theorem IsSDS.sum_contract_sq {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) :
    (∑ h, contract φ D h) ^ 2 = k + lam * ((c : ℤ) * Fintype.card H - 1) := by
  set a := contract φ D
  have hshift (x : H) : ∑ g, a (x + g) = ∑ h, a h :=
    Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
  have e : (∑ h, a h) ^ 2 = ∑ g, ∑ h, a h * a (h + g) := by
    rw [sq, Finset.sum_mul, Finset.sum_comm]
    simp only [← Finset.mul_sum, hshift]
  have hauto (g : H) : ∑ h, a h * a (h + g) =
      (if g = 0 then (k : ℤ) - lam else 0) + lam * c := by
    by_cases hg : g = 0
    · subst hg
      simp only [add_zero, ite_true]
      rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
        Nat.cast_one]
      ring
    · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcard, ite_eq_right hg, zero_add]
  rw [e, Finset.sum_congr rfl fun g _ => hauto g, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp
  ring

omit [DecidableEq H] in
/-- C6, arithmetic part: no SDS when, under C5's hypotheses without `2c < p^j`, every sign
sum `s' = ±s` and residue `0 ≤ t₀ < p^j` fails the moments test. -/
theorem not_hasSDS_of_moments (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) {p i j : ℕ} [Fact p.Prime] (hi : 0 < i)
    (hc : ∀ h : H, p ^ i • h = -h) (hH : (Fintype.card H : ZMod p) ≠ 0) (hH1 : ∃ g : H, g ≠ 0)
    {k : ℕ} {lam : ℤ} (hn : (p : ℤ) ^ (2 * j) ∣ k - lam) (hk : (k : ℤ) ≠ lam) {s : ℤ}
    (hs : s ^ 2 = k + lam * ((c : ℤ) * Fintype.card H - 1))
    (hfail : ∀ s' ∈ [s, -s], ∀ t0 ∈ Finset.Ico (0 : ℤ) ((p : ℤ) ^ j),
      ¬ MomentsOk (Fintype.card H) ((p : ℤ) ^ j) s' (k + lam * ((c : ℤ) - 1)) t0) :
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
  have hok := momentsOk_of_congr a hq ht (hD.exists_contract_ne φ hφ hcard hH1 hk)
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
