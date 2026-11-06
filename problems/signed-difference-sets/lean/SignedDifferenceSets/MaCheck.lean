module

public import SignedDifferenceSets.LinearMaps
public import SignedDifferenceSets.MaRule
public import SignedDifferenceSets.PolyCert
public import SignedDifferenceSets.SelfConjugacyCheck

/-!
# Checking C21 on the table's rows

A certificate for a row (group `Grp ms`, `k`, `λ`) names a prime `p`, `r = p^(j−1)` (the quotient
is `ZMod (r p) × Grp ks`), `i` with `p^i ≡ −1` on `Grp ks`, `e` with `p^e ∣ k − λ`, `b`, and the
quotient map as forms `A`, one per factor of `r p :: ks` (`LinearMaps.lean`), with preimages `P`
of the unit vectors. `MaRowCert.Kills` is plain arithmetic; `MaRowCert.not_hasSDS` turns a kill
into `¬ HasSDS`, given `MaRule` and `CycloFacts p r` (`PolyCert.lean`).
-/

@[expose] public section

namespace SignedDifferenceSets

/-- A C21 certificate (`ks ≠ []`; `[1]` for a trivial `K`). -/
structure MaRowCert where
  p : ℕ
  r : ℕ
  i : ℕ
  e : ℕ
  b : ℕ
  ks : List ℕ
  A : List (List ℕ)
  P : List (List ℕ)
  deriving DecidableEq

/-- C21's hypotheses on the row, `c = |G| / (r p |K|)`. -/
def MaRowCert.Kills (w : Row) (c : MaRowCert) : Prop :=
  IsPrimeTD c.p ∧ 0 < c.r ∧ 0 < c.i ∧ (∀ m ∈ w.ms, 0 < m) ∧ c.ks ≠ [] ∧
    (∀ d ∈ c.ks, d ∣ c.p ^ c.i + 1) ∧ MapOk w.ms (c.r * c.p :: c.ks) c.A ∧
    SurjCert w.ms (c.r * c.p :: c.ks) c.A c.P ∧ c.r * c.p * c.ks.prod ∣ w.ms.prod ∧
    (c.p : ℤ) ^ c.e ∣ w.k - w.lam ∧ (w.k : ℤ) ≠ w.lam ∧ 2 * c.b ≤ c.e ∧
    2 * (w.ms.prod / (c.r * c.p * c.ks.prod)) < c.p ^ c.b

instance (w : Row) (c : MaRowCert) : Decidable (c.Kills w) := by
  unfold MaRowCert.Kills; infer_instance

/-- C21 on a quotient `ZMod (r p) × Grp ks` given by forms. -/
theorem not_hasSDS_of_maRule (hrule : MaRule) {ms ks : List ℕ} {p r i e b k : ℕ} {lam : ℤ}
    {A P : List (List ℕ)} (hp : p.Prime) (hr : 0 < r) (hi : 0 < i) (hne : ks ≠ [])
    (hks : ∀ d ∈ ks, d ∣ p ^ i + 1) (hmap : MapOk ms (r * p :: ks) A)
    (hsurj : SurjCert ms (r * p :: ks) A P) (hprod : r * p * ks.prod ∣ ms.prod)
    (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam) (hk : (k : ℤ) ≠ lam) (hbe : 2 * b ≤ e)
    (hc : 2 * (ms.prod / (r * p * ks.prod)) < p ^ b) (hcyc : CycloFacts p r)
    (inst : Fintype (Grp ms)) : ¬ @HasSDS (Grp ms) _ inst k lam := by
  obtain ⟨k₀, ks, rfl⟩ := List.exists_cons_of_ne_nil hne
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero (r * p) := ⟨(Nat.mul_pos hr hp.pos).ne'⟩
  let _ : Fintype (Grp (k₀ :: ks)) :=
    Grp.fintype _ fun d hd => Nat.pos_of_dvd_of_pos (hks d hd) (by positivity)
  let φ : Grp ms →+ ZMod (r * p) × Grp (k₀ :: ks) := linMap ms (r * p :: k₀ :: ks) A hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp ms) =
      ms.prod / (r * p * (k₀ :: ks).prod) * Fintype.card (ZMod (r * p) × Grp (k₀ :: ks)) := by
    rw [Fintype.card_prod, ZMod.card, Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hconj (x : Grp (k₀ :: ks)) : p ^ i • x = -x := by
    have := Grp.nsmul_eq_zero (N := p ^ i + 1) (k₀ :: ks) hks x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  exact hrule (Grp ms) (Grp (k₀ :: ks)) p r i e b _ k lam φ hφ hcard hr hi hconj hn hk hbe hc
    fun S _ x hx => hcyc S x hx

/-- A killed row has no SDS, given C21 and the cyclotomic facts at `(p, r)`. -/
theorem MaRowCert.not_hasSDS (hrule : MaRule) {w : Row} {c : MaRowCert} (h : c.Kills w)
    (hcyc : CycloFacts c.p c.r) (inst : Fintype (Grp w.ms)) :
    ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨hp, hr, hi, -, hne, hks, hmap, hsurj, hprod, hn, hk, hbe, hc⟩ := h
  exact not_hasSDS_of_maRule hrule hp.prime hr hi hne hks hmap hsurj hprod hn hk hbe hc hcyc inst

end SignedDifferenceSets
