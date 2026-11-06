module

public import Mathlib
public import SignedDifferenceSets.Contraction

/-!
# Self-conjugacy on a quotient (C5)

Let `p` be a prime with `p^(2j) ∣ k − λ`, and `H` a nontrivial quotient of `G` (fibres of size
`c`) with `|H|` prime to `p` on which `p^i h = −h` for some `i ≥ 1` (`p` self-conjugate mod
`exp H`). Then the coset sums of an SDS agree mod `p^j` (Turyn 1965, Lemma 3, here elementary):
for `j = 1`, `y = ∑ (a_h − t)[h]` in `F_p[H]` has `y^(p^i) = ȳ` (Frobenius) and `y ȳ = 0`, so
`y = y^(p^(2i)) = 0`; for `j > 1`, induction on `(a − t)/p`. If moreover `2c < p^j`, all coset
sums are equal, forcing `k = λ`: no SDS.
-/

@[expose] public section

open AddMonoidAlgebra

namespace SignedDifferenceSets

section Alg

variable {H : Type*} [AddCommGroup H] [Fintype H] {p : ℕ} [hp : Fact p.Prime]

/-- `∑_h b h · [h]` in `F_p[H]`. -/
noncomputable def toAlg (b : H → ZMod p) : AddMonoidAlgebra (ZMod p) H := ∑ h, single h (b h)

instance : CharP (AddMonoidAlgebra (ZMod p) H) p :=
  charP_of_injective_algebraMap (R := ZMod p) (by
    intro x y hxy
    simpa using hxy) p

omit [AddCommGroup H] in
theorem coeff_toAlg (b : H → ZMod p) (g : H) : (toAlg b).coeff g = b g := by
  classical
  simp [toAlg, coeff_sum, coeff_single, Finsupp.single_apply]

theorem eq_zero_of_toAlg_eq_zero {b : H → ZMod p} (h : toAlg b = 0) : b = 0 := by
  funext g
  simpa [coeff_toAlg] using congrArg (fun x => x.coeff g) h

/-- Frobenius: `(∑ b h [h])^(p^N) = ∑ b h [p^N h]`. -/
theorem toAlg_pow (b : H → ZMod p) (N : ℕ) :
    toAlg b ^ p ^ N = ∑ h, single (p ^ N • h) (b h) := by
  rw [toAlg, sum_pow_char_pow]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [AddMonoidAlgebra.single_pow, ZMod.pow_card_pow]

/-- With `p^i h = -h` on `H`, the `p^i`-th power is the conjugate `∑ b(-h) [h]`. -/
theorem toAlg_pow_conj {i : ℕ} (hc : ∀ h : H, p ^ i • h = -h) (b : H → ZMod p) :
    toAlg b ^ p ^ i = toAlg (fun h => b (-h)) := by
  rw [toAlg_pow, toAlg]
  simp only [hc]
  exact Fintype.sum_equiv (Equiv.neg H) _ _ (fun h => by simp)

/-- `y · ȳ` has the autocorrelations of `b` as coefficients. -/
theorem toAlg_mul_conj (b : H → ZMod p) :
    toAlg b * toAlg (fun h => b (-h)) = ∑ g, single g (∑ h, b h * b (h + g)) := by
  simp only [toAlg, Finset.sum_mul_sum, single_mul_single]
  calc ∑ x, ∑ z, single (x + z) (b x * b (-z))
      = ∑ x, ∑ h, single (x - h) (b x * b h) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Fintype.sum_equiv (Equiv.neg H) _ _ (fun z => by simp [sub_eq_add_neg])
    _ = ∑ h, ∑ x, single (x - h) (b x * b h) := Finset.sum_comm
    _ = ∑ h, ∑ g, single g (b (h + g) * b h) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        exact Fintype.sum_equiv (Equiv.subRight h) _ _ (fun x => by simp)
    _ = ∑ g, ∑ h, single g (b (h + g) * b h) := Finset.sum_comm
    _ = ∑ g, single g (∑ h, b h * b (h + g)) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        have e := map_sum (singleAddHom (R := ZMod p) g) (fun h => b h * b (h + g)) Finset.univ
        simp only [singleAddHom_apply] at e
        rw [e]
        exact Finset.sum_congr rfl fun h _ => by rw [mul_comm]

/-- The core of C5 (j = 1): a vector over `F_p` on `H` with autocorrelation `0` at every
shift is `0` when `p^i h = -h` on `H` for some `i ≥ 1`. -/
theorem eq_zero_of_autocorr {i : ℕ} (hi : 0 < i) (hc : ∀ h : H, p ^ i • h = -h)
    (b : H → ZMod p) (hb : ∀ g, ∑ h, b h * b (h + g) = 0) : b = 0 := by
  apply eq_zero_of_toAlg_eq_zero
  set y := toAlg b with hy
  have h1 : y * y ^ p ^ i = 0 := by
    rw [toAlg_pow_conj hc, toAlg_mul_conj]
    simp [hb]
  have h2 : y ^ (p ^ i * p ^ i) = y := by
    rw [pow_mul, toAlg_pow_conj hc, toAlg_pow_conj hc]
    simp only [neg_neg]
    rfl
  have hp2 : 2 ≤ p ^ i := by
    calc 2 ≤ p := hp.out.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ i := Nat.pow_le_pow_right hp.out.pos hi
  obtain ⟨m, hm⟩ : ∃ m, p ^ i * p ^ i = (1 + p ^ i) + m :=
    ⟨p ^ i * p ^ i - (1 + p ^ i), by
      nlinarith [Nat.sub_add_cancel (show 1 + p ^ i ≤ p ^ i * p ^ i by nlinarith)]⟩
  rw [← h2, hm, pow_add, pow_add, pow_one, h1, zero_mul]

end Alg

section Congr

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H] {p : ℕ} [hp : Fact p.Prime]

omit [DecidableEq H] in
/-- Integer vectors whose autocorrelations agree mod `p` at every shift are constant mod `p`,
when `|H|` is a unit mod `p` and `p^i h = -h` on `H` (`i ≥ 1`). -/
theorem congr_of_autocorr {i : ℕ} (hi : 0 < i) (hc : ∀ h : H, p ^ i • h = -h)
    (hH : (Fintype.card H : ZMod p) ≠ 0) (a : H → ℤ) (C : ℤ)
    (ha : ∀ g, ((∑ h, a h * a (h + g) : ℤ) : ZMod p) = C) (h h' : H) :
    (a h : ZMod p) = a h' := by
  set A : H → ZMod p := fun h => a h
  set S := ∑ h, A h
  set t := S / Fintype.card H
  have hA (g : H) : ∑ h, A h * A (h + g) = C := by simpa [A] using ha g
  have hshift (g : H) : ∑ h, A (h + g) = S :=
    Fintype.sum_equiv (Equiv.addRight g) _ _ (fun _ => rfl)
  have hshift' (x : H) : ∑ g, A (x + g) = S :=
    Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
  have hS : S * S = Fintype.card H * C := by
    calc S * S = ∑ h, A h * S := by rw [← Finset.sum_mul]
      _ = ∑ h, A h * ∑ g, A (h + g) := by simp only [hshift']
      _ = ∑ g, ∑ h, A h * A (h + g) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
      _ = Fintype.card H * C := by simp [hA]
  have hSt : S = Fintype.card H * t := by
    simp only [t]; field_simp
  have hb : ∀ g, ∑ h, (A h - t) * (A (h + g) - t) = 0 := by
    intro g
    have e : ∑ h, (A h - t) * (A (h + g) - t) =
        ∑ h, A h * A (h + g) - t * ∑ h, A (h + g) - t * S + Fintype.card H * t * t := by
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, S]
      simp [Finset.sum_const, Finset.card_univ]
      ring_nf
    rw [e, hA, hshift]
    have hC : (Fintype.card H : ZMod p) * C = Fintype.card H * (Fintype.card H * t * t) := by
      rw [← hS, hSt]; ring
    have hC' : C = Fintype.card H * t * t := mul_left_cancel₀ hH hC
    rw [hC', hSt]; ring
  have h0 := eq_zero_of_autocorr hi hc (fun h => A h - t) hb
  have e1 := congrFun h0 h
  have e2 := congrFun h0 h'
  simp only [Pi.zero_apply, sub_eq_zero] at e1 e2
  exact e1.trans e2.symm

/-- C5 by induction on `j`: integer vectors with autocorrelation `n·[g = 0] + μ` are constant
mod `p^j` when `p^(2j) ∣ n` (Turyn's self-conjugacy bound, elementary form). -/
theorem congr_pow_of_autocorr {i : ℕ} (hi : 0 < i) (hc : ∀ h : H, p ^ i • h = -h)
    (hH : (Fintype.card H : ZMod p) ≠ 0) (hH1 : ∃ g : H, g ≠ 0) :
    ∀ (j : ℕ) (a : H → ℤ) (n μ : ℤ),
      (∀ g, ∑ h, a h * a (h + g) = (if g = 0 then n else 0) + μ) →
      (p : ℤ) ^ (2 * j) ∣ n → ∀ h h', a h ≡ a h' [ZMOD (p : ℤ) ^ j]
  | 0, a, n, μ, _, _, h, h' => by simp [Int.modEq_one]
  | j + 1, a, n, μ, ha, hn, h, h' => by
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    obtain ⟨q, hq⟩ := hn
    have h1 (x : H) : (a x : ZMod p) = a 0 := by
      refine congr_of_autocorr hi hc hH a μ (fun g => ?_) x 0
      rw [ha g]
      split_ifs
      · rw [hq]; push_cast; simp
      · simp
    have hdiv (x : H) : (p : ℤ) ∣ a x - a 0 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h1 x).symm
    choose a' ha' using hdiv
    set t := a 0
    set S := ∑ x, a x
    have hshift (g : H) : ∑ x, a (x + g) = S :=
      Fintype.sum_equiv (Equiv.addRight g) _ _ (fun _ => rfl)
    have key (g : H) : (p : ℤ) ^ 2 * ∑ x, a' x * a' (x + g) =
        (if g = 0 then n else 0) + (μ - 2 * t * S + Fintype.card H * t ^ 2) := by
      have e (x : H) : (p : ℤ) ^ 2 * (a' x * a' (x + g)) =
          a x * a (x + g) - t * a (x + g) - t * a x + t ^ 2 := by
        have := ha' x; have := ha' (x + g)
        linear_combination (-(a (x + g)) + t) * ha' x - (p * a' x) * ha' (x + g)
      rw [Finset.mul_sum, Finset.sum_congr rfl fun x _ => e x]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ha g, hshift,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    obtain ⟨g0, hg0⟩ := hH1
    set μ' := ∑ x, a' x * a' (x + g0)
    have hμ' : (p : ℤ) ^ 2 * μ' = μ - 2 * t * S + Fintype.card H * t ^ 2 := by
      rw [key g0, ite_eq_right hg0, zero_add]
    have ha2 (g : H) : ∑ x, a' x * a' (x + g) =
        (if g = 0 then (p : ℤ) ^ (2 * j) * q else 0) + μ' := by
      have hk := key g
      rw [← hμ', hq] at hk
      apply mul_left_cancel₀ (pow_ne_zero 2 hp0)
      rw [hk]
      split_ifs <;> ring
    have ih := congr_pow_of_autocorr hi hc hH ⟨g0, hg0⟩ j a' _ μ' ha2 (dvd_mul_right _ _) h h'
    rw [Int.modEq_iff_dvd] at ih ⊢
    have e : a h' - a h = p * (a' h' - a' h) := by linear_combination ha' h' - ha' h
    rw [e, pow_succ, mul_comm ((p : ℤ) ^ j)]
    exact mul_dvd_mul_left _ ih

end Congr


variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H] [DecidableEq H]

omit [AddCommGroup H] [DecidableEq H] in
theorem one_le_of_card {c : ℕ} (hcard : Fintype.card G = c * Fintype.card H) : 1 ≤ c := by
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · have := Fintype.card_pos (α := G)
    rw [hcard, h0, zero_mul] at this
    omega
  · exact h0

/-- C5: the coset sums of an SDS on a self-conjugate quotient agree mod `p^j` when
`p^(2j) ∣ k − λ`. -/
theorem IsSDS.contract_congr_pow {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ} (hcard : Fintype.card G = c * Fintype.card H)
    {p i j : ℕ} [Fact p.Prime] (hi : 0 < i) (hc : ∀ h : H, p ^ i • h = -h)
    (hH : (Fintype.card H : ZMod p) ≠ 0) (hH1 : ∃ g : H, g ≠ 0)
    (hn : (p : ℤ) ^ (2 * j) ∣ k - lam) (h h' : H) :
    contract φ D h ≡ contract φ D h' [ZMOD (p : ℤ) ^ j] := by
  refine congr_pow_of_autocorr hi hc hH hH1 j _ (k - lam) (lam * c) (fun g => ?_) hn h h'
  by_cases hg : g = 0
  · subst hg
    simp only [add_zero, ite_true]
    rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard), Nat.cast_one]
    ring
  · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcard, ite_eq_right hg, zero_add]

omit [DecidableEq H] in
/-- Rule SC (C5): no SDS when `p^(2j) ∣ k − λ ≠ 0` for a prime `p` self-conjugate on a
nontrivial quotient `H` of order prime to `p` whose fibres `c` satisfy `2c < p^j`. -/
theorem not_hasSDS_of_selfConj (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) {p i j : ℕ} [Fact p.Prime] (hi : 0 < i)
    (hc : ∀ h : H, p ^ i • h = -h) (hH : (Fintype.card H : ZMod p) ≠ 0) (hH1 : ∃ g : H, g ≠ 0)
    {k : ℕ} {lam : ℤ} (hn : (p : ℤ) ^ (2 * j) ∣ k - lam) (hk : (k : ℤ) ≠ lam) (hp : 2 * c < p ^ j) :
    ¬ HasSDS G k lam := by
  classical
  rintro ⟨D, hD⟩
  have hb (h : H) : |contract φ D h| ≤ c := by
    have := abs_contract_le φ D h
    rwa [card_fibre_eq hφ hcard] at this
  have hconst (h : H) : contract φ D h = contract φ D 0 := by
    have e := hD.contract_congr_pow φ hφ hcard hi hc hH hH1 hn 0 h
    rw [Int.modEq_iff_dvd] at e
    have hlt : |contract φ D h - contract φ D 0| < (p : ℤ) ^ j := by
      have := abs_sub (contract φ D h) (contract φ D 0)
      have := hb 0
      have := hb h
      have : (2 * c : ℤ) < (p : ℤ) ^ j := by exact_mod_cast hp
      linarith
    have := Int.eq_zero_of_abs_lt_dvd e hlt
    linarith
  obtain ⟨g, hg⟩ := hH1
  have e1 := hD.contract_autocorr φ g hg
  have e2 := hD.contract_sq φ
  rw [Finset.sum_congr rfl fun h _ => by rw [hconst h, hconst (h + g)]] at e1
  rw [Finset.sum_congr rfl fun h _ => by rw [hconst h]] at e2
  rw [card_fibre_eq hφ hcard] at e1 e2
  rw [Nat.cast_sub (one_le_of_card hcard), Nat.cast_one] at e2
  apply hk
  linear_combination e1 - e2

end SignedDifferenceSets
