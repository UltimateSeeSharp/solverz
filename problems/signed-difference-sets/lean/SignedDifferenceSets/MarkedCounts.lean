module

public import SignedDifferenceSets.Box

/-!
# Marked counts per coset (C7)

Under C5's hypotheses (as in C13, C14) every coset sum `a_h` lies in
`V = {x : |x| ≤ c, x ≡ t₀ (mod q)}`. The coset of `h` holds `m_h` marked elements with
`|a_h| ≤ m_h ≤ c`, `m_h ≡ a_h (mod 2)` and `Σ m_h = k`, so `Σ |a_h| ≤ k ≤ Σ maxm(a_h)`, where
`maxm(x)` is `c` or `c − 1`, whichever has `x`'s parity. Weights `(α, β, γ, d)`, `d ≥ 0`, with
`γ + βx + αx² ≤ d|x|` on `V` and `γN + βs' + αQ > dk` contradict the first bound; with
`d·maxm(x) ≤ γ + βx + αx²` on `V` and `γN + βs' + αQ < dk` the second. By LP duality such
weights exist whenever no real counts on `V` with the moments `N`, `s'`, `Q` meet both bounds.
A row dies when every `s' = ±s` and `t₀` fails C14's test or has such weights.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- The most marked elements a coset of size `c` with sum `x` holds: `c` or `c − 1`, whichever
has `x`'s parity. -/
def maxMarked (c x : ℤ) : ℤ := if (c - x) % 2 = 0 then c else c - 1

/-- Weights `(α, β, γ, d)`: the quadratic `γ + βx + αx²` against `d` times a bound. -/
structure Weights where
  α : ℤ
  β : ℤ
  γ : ℤ
  d : ℤ
  deriving DecidableEq

/-- The quadratic `γ + βx + αx²`. -/
def Weights.eval (w : Weights) (x : ℤ) : ℤ := w.γ + w.β * x + w.α * x ^ 2

/-- The quadratic summed over `N` values with sum `s'` and square sum `Q`. -/
def Weights.total (w : Weights) (N s' Q : ℤ) : ℤ := w.γ * N + w.β * s' + w.α * Q

/-- Lower certificate: on `x ≡ t₀ (mod q)` in `[−c, c]` the quadratic is at most `d|x|`, but
its total over `N` values with moments `s'`, `Q` exceeds `dk`. -/
def Weights.Lower (w : Weights) (N q s' Q t0 c k : ℤ) : Prop :=
  0 ≤ w.d ∧ (∀ x, |x| ≤ c → q ∣ x - t0 → w.eval x ≤ w.d * |x|) ∧ w.d * k < w.total N s' Q

/-- Upper certificate: on `x ≡ t₀ (mod q)` in `[−c, c]` the quadratic is at least
`d·maxMarked c x`, but its total over `N` values with moments `s'`, `Q` is below `dk`. -/
def Weights.Upper (w : Weights) (N q s' Q t0 c k : ℤ) : Prop :=
  0 ≤ w.d ∧ (∀ x, |x| ≤ c → q ∣ x - t0 → w.d * maxMarked c x ≤ w.eval x) ∧
    w.total N s' Q < w.d * k

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]
  [DecidableEq H]

/-- The number of marked elements in the coset of `h`. -/
def marked (φ : G →+ H) (D : G → SignType) (h : H) : ℕ :=
  ((fibre φ h).filter fun x => D x ≠ 0).card

omit [Fintype H] in
theorem marked_eq_sum_abs (φ : G →+ H) (D : G → SignType) (h : H) :
    (marked φ D h : ℤ) = ∑ x ∈ fibre φ h, |(D x : ℤ)| := by
  rw [marked, Finset.card_filter, Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [abs_sign_eq]; split_ifs <;> simp_all

omit [Fintype H] in
/-- A coset sum is at most the coset's marked count in absolute value. -/
theorem abs_contract_le_marked (φ : G →+ H) (D : G → SignType) (h : H) :
    |contract φ D h| ≤ marked φ D h := by
  rw [marked_eq_sum_abs]
  exact Finset.abs_sum_le_sum_abs _ _

omit [Fintype H] in
/-- A coset holds at most its size in marked elements. -/
theorem marked_le_card (φ : G →+ H) (D : G → SignType) (h : H) :
    marked φ D h ≤ (fibre φ h).card :=
  Finset.card_filter_le _ _

omit [Fintype H] in
/-- A coset's marked count and sum have the same parity. -/
theorem even_marked_sub_contract (φ : G →+ H) (D : G → SignType) (h : H) :
    Even ((marked φ D h : ℤ) - contract φ D h) := by
  rw [marked_eq_sum_abs]
  unfold contract fibre
  rw [← Finset.sum_sub_distrib]
  exact Finset.even_sum _ fun x _ => by cases D x <;> simp

/-- The marked counts of an SDS add up to `k`. -/
theorem IsSDS.sum_marked {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) : ∑ h, (marked φ D h : ℤ) = k := by
  simp only [marked_eq_sum_abs]
  rw [sum_fibre, hD.sum_abs]

omit [Fintype H] in
/-- A coset of size at most `c` holds at most `maxMarked c` of its sum marked elements. -/
theorem marked_le_maxMarked (φ : G →+ H) (D : G → SignType) (h : H) {c : ℤ}
    (hc : (marked φ D h : ℤ) ≤ c) : (marked φ D h : ℤ) ≤ maxMarked c (contract φ D h) := by
  unfold maxMarked
  split_ifs with hpar
  · exact hc
  · have hne : (marked φ D h : ℤ) ≠ c := by
      rintro e
      exact hpar (by rw [← e]; exact Int.even_iff.1 (even_marked_sub_contract φ D h))
    omega

omit [DecidableEq H] in
/-- C7: no SDS when, under C5's hypotheses, every sign sum `s' = ±s` and residue
`0 ≤ t₀ < p^j` fails C14's box test or has lower or upper weights. -/
theorem not_hasSDS_of_marked (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) {p i j : ℕ} [Fact p.Prime] (hi : 0 < i)
    (hc : ∀ h : H, p ^ i • h = -h) (hH : (Fintype.card H : ZMod p) ≠ 0) (hH1 : ∃ g : H, g ≠ 0)
    {k : ℕ} {lam : ℤ} (hn : (p : ℤ) ^ (2 * j) ∣ k - lam) (hk : (k : ℤ) ≠ lam) {s : ℤ}
    (hs : s ^ 2 = k + lam * ((c : ℤ) * Fintype.card H - 1))
    (hfail : ∀ s' ∈ [s, -s], ∀ t0 ∈ Finset.Ico (0 : ℤ) ((p : ℤ) ^ j),
      ¬ BoxOk (Fintype.card H) ((p : ℤ) ^ j) s' (k + lam * ((c : ℤ) - 1)) t0 c ∨
        ∃ w : Weights,
          w.Lower (Fintype.card H) ((p : ℤ) ^ j) s' (k + lam * ((c : ℤ) - 1)) t0 c k ∨
            w.Upper (Fintype.card H) ((p : ℤ) ^ j) s' (k + lam * ((c : ℤ) - 1)) t0 c k) :
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
  have hm (h : H) : (marked φ D h : ℤ) ≤ c := by
    have := marked_le_card φ D h
    rw [card_fibre_eq hφ hcard] at this
    exact_mod_cast this
  have hQ : ∑ h, a h * a h = k + lam * ((c : ℤ) - 1) := by
    rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
      Nat.cast_one]
  have hsq := hD.sum_contract_sq φ hφ hcard
  rw [← hs] at hsq
  have hmem : ∑ h, a h ∈ [s, -s] := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · exact List.mem_cons.2 (Or.inl h)
    · exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 h))
  have htot (w : Weights) : ∑ h, w.eval (a h) =
      w.total (Fintype.card H) (∑ h, a h) (k + lam * ((c : ℤ) - 1)) := by
    rw [← hQ]
    simp only [Weights.eval, Weights.total, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sq]
    ring
  have ht0 : a 0 % q ∈ Finset.Ico (0 : ℤ) q :=
    Finset.mem_Ico.2 ⟨Int.emod_nonneg _ hq.ne', Int.emod_lt_of_pos _ hq⟩
  rcases hfail _ hmem _ ht0 with hbox | ⟨w, ⟨hd, hle, hlt⟩ | ⟨hd, hle, hlt⟩⟩
  · have hok := boxOk_of_congr a hq ht (hD.exists_contract_ne φ hφ hcard hH1 hk) hb
    rw [hQ] at hok
    exact hbox hok
  · have h1 : ∑ h, w.eval (a h) ≤ w.d * k :=
      calc ∑ h, w.eval (a h) ≤ ∑ h, w.d * |a h| :=
            Finset.sum_le_sum fun h _ => hle _ (hb h) (ht h)
        _ = w.d * ∑ h, |a h| := (Finset.mul_sum _ _ _).symm
        _ ≤ w.d * k := mul_le_mul_of_nonneg_left (hD.sum_abs_contract_le φ) hd
    rw [htot] at h1
    exact absurd hlt (not_lt.2 h1)
  · have h1 : w.d * k ≤ ∑ h, w.eval (a h) :=
      calc w.d * k = w.d * ∑ h, (marked φ D h : ℤ) := by rw [hD.sum_marked φ]
        _ ≤ w.d * ∑ h, maxMarked c (a h) :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun h _ => marked_le_maxMarked φ D h (hm h)) hd
        _ = ∑ h, w.d * maxMarked c (a h) := Finset.mul_sum _ _ _
        _ ≤ ∑ h, w.eval (a h) := Finset.sum_le_sum fun h _ => hle _ (hb h) (ht h)
    rw [htot] at h1
    exact absurd hlt (not_lt.2 h1)

end SignedDifferenceSets
