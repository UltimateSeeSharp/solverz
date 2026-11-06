module

public import SignedDifferenceSets.Box
public import SignedDifferenceSets.SelfConjugacyCheck

/-!
# C23: self-conjugacy with a composite modulus

C5 makes the coset sums agree mod `p ^ j` for each prime `p` self-conjugate on `H`; distinct
primes give coprime moduli, so the sums agree mod their product `q` and C14's box test runs
with `q` (`not_hasSDS_of_compositeModulus`). A certificate (`CmCert`: quotient, primes with
their exponents, sign sum) is checked per row by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets

variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]

/-- C5's hypotheses on `H` for `x = (p, i, j)`: `p` prime, `p ^ i ≡ −1` on `H`, `p ∤ |H|`,
`p ^ (2j) ∣ k − λ`. -/
def SelfConjOn (H : Type*) [AddCommGroup H] [Fintype H] (k : ℕ) (lam : ℤ) (x : ℕ × ℕ × ℕ) :
    Prop :=
  x.1.Prime ∧ 0 < x.2.1 ∧ (∀ h : H, x.1 ^ x.2.1 • h = -h) ∧
    (Fintype.card H : ZMod x.1) ≠ 0 ∧ (x.1 : ℤ) ^ (2 * x.2.2) ∣ k - lam

/-- The product of the moduli `p ^ j`. -/
def modulusProd (L : List (ℕ × ℕ × ℕ)) : ℤ := (L.map fun x => (x.1 : ℤ) ^ x.2.2).prod

theorem isCoprime_modulusProd {p j : ℕ} (hp : p.Prime) :
    ∀ L : List (ℕ × ℕ × ℕ), (∀ x ∈ L, x.1.Prime ∧ p ≠ x.1) →
      IsCoprime ((p : ℤ) ^ j) (modulusProd L)
  | [], _ => by simp [modulusProd]
  | x :: L, h => by
    have hx := h x List.mem_cons_self
    have ih := isCoprime_modulusProd hp L fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [modulusProd, List.map_cons, List.prod_cons] at ih ⊢
    exact IsCoprime.mul_right (IsCoprime.pow (Nat.isCoprime_iff_coprime.2
      ((Nat.coprime_primes hp hx.1).2 hx.2))) ih

theorem modulusProd_pos {L : List (ℕ × ℕ × ℕ)} (h : ∀ x ∈ L, x.1.Prime) : 0 < modulusProd L :=
  List.prod_pos fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact pow_pos (by exact_mod_cast (h x hx).pos) _

variable [DecidableEq H]

/-- C23's congruence: the coset sums agree mod the product of C5's moduli. -/
theorem IsSDS.modulusProd_dvd {k : ℕ} {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D)
    (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) (hH1 : ∃ g : H, g ≠ 0) (h h' : H) :
    ∀ L : List (ℕ × ℕ × ℕ), (∀ x ∈ L, SelfConjOn H k lam x) →
      L.Pairwise (fun x y => x.1 ≠ y.1) → modulusProd L ∣ contract φ D h - contract φ D h'
  | [], _, _ => by simp [modulusProd]
  | x :: L, hL, hpw => by
    obtain ⟨hp, hi, hc, hH, hn⟩ := hL x List.mem_cons_self
    have : Fact x.1.Prime := ⟨hp⟩
    have h1 : (x.1 : ℤ) ^ x.2.2 ∣ contract φ D h - contract φ D h' :=
      Int.modEq_iff_dvd.1 (hD.contract_congr_pow φ hφ hcard hi hc hH hH1 hn h' h)
    have h2 := hD.modulusProd_dvd φ hφ hcard hH1 h h' L
      (fun y hy => hL y (List.mem_cons_of_mem _ hy)) (List.pairwise_cons.1 hpw).2
    have hcop := isCoprime_modulusProd (j := x.2.2) hp L fun y hy =>
      ⟨(hL y (List.mem_cons_of_mem _ hy)).1, (List.pairwise_cons.1 hpw).1 y hy⟩
    simp only [modulusProd, List.map_cons, List.prod_cons] at h2 hcop ⊢
    exact hcop.mul_dvd h1 h2

omit [DecidableEq H] in
/-- C23: no SDS when, for primes `L` each meeting C5's hypotheses on `H` and `q` the product
of their `p ^ j`, every sign sum `s' = ±s` and residue `0 ≤ t₀ < q` fails C14's box test. -/
theorem not_hasSDS_of_compositeModulus (φ : G →+ H) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card H) (hH1 : ∃ g : H, g ≠ 0) {k : ℕ} {lam : ℤ}
    (hk : (k : ℤ) ≠ lam) {L : List (ℕ × ℕ × ℕ)} (hL : ∀ x ∈ L, SelfConjOn H k lam x)
    (hpw : L.Pairwise fun x y => x.1 ≠ y.1) {s : ℤ}
    (hs : s ^ 2 = k + lam * ((c : ℤ) * Fintype.card H - 1))
    (hfail : ∀ s' ∈ [s, -s], ∀ t0 ∈ Finset.Ico (0 : ℤ) (modulusProd L),
      ¬ BoxOk (Fintype.card H) (modulusProd L) s' (k + lam * ((c : ℤ) - 1)) t0 c) :
    ¬ HasSDS G k lam := by
  classical
  rintro ⟨D, hD⟩
  set a := contract φ D
  set q := modulusProd L
  have hq : 0 < q := modulusProd_pos fun x hx => (hL x hx).1
  have hcong (h : H) : a h ≡ a 0 [ZMOD q] :=
    Int.modEq_iff_dvd.2 (hD.modulusProd_dvd φ hφ hcard hH1 0 h L hL hpw)
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

/-- A C23 certificate: the quotient `Grp ds`, the primes `(p, i, j)` and the sign sum `s`. -/
structure CmCert where
  ds : List ℕ
  ps : List (ℕ × ℕ × ℕ)
  s : ℤ
  deriving DecidableEq

/-- The row's arithmetic, C5's hypotheses for every prime, and C14's test failing with
`q = ∏ p ^ j` for both signs and every residue. -/
def CmCert.Kills (r : Row) (c : CmCert) : Prop :=
  (∀ m ∈ r.ms, 0 < m) ∧ Dvds c.ds r.ms ∧ 1 < c.ds.prod ∧ (r.k : ℤ) ≠ r.lam ∧
    (∀ x ∈ c.ps, IsPrimeTD x.1 ∧ 0 < x.2.1 ∧ (∀ d ∈ c.ds, d ∣ x.1 ^ x.2.1 + 1) ∧
      ¬ x.1 ∣ c.ds.prod ∧ (x.1 : ℤ) ^ (2 * x.2.2) ∣ r.k - r.lam) ∧
    c.ps.Pairwise (fun x y => x.1 ≠ y.1) ∧ c.s ^ 2 = r.k + r.lam * ((r.ms.prod : ℤ) - 1) ∧
    ∀ s' ∈ [c.s, -c.s], ∀ t ∈ List.range (modulusProd c.ps).toNat,
      ¬ BoxOk c.ds.prod (modulusProd c.ps) s'
        (r.k + r.lam * (((r.ms.prod / c.ds.prod : ℕ) : ℤ) - 1)) t
        ((r.ms.prod / c.ds.prod : ℕ) : ℤ)

instance CmCert.instDecidableKills (r : Row) (c : CmCert) : Decidable (c.Kills r) := by
  unfold CmCert.Kills; infer_instance

/-- A row C23 kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem CmCert.not_hasSDS {r : Row} {c : CmCert} (h : c.Kills r) (inst : Fintype (Grp r.ms)) :
    ¬ @HasSDS (Grp r.ms) _ inst r.k r.lam := by
  obtain ⟨hms, hdv, hH1, hk, hps, hpw, hs, hfail⟩ := h
  let _ : Fintype (Grp c.ds) := Grp.fintype c.ds (Dvds.pos _ _ hdv hms)
  have hprod := Dvds.prod_dvd _ _ hdv
  have hcard : Fintype.card (Grp r.ms) =
      (r.ms.prod / c.ds.prod) * Fintype.card (Grp c.ds) := by
    rw [Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hL : ∀ x ∈ c.ps, SelfConjOn (Grp c.ds) r.k r.lam x := by
    intro x hx
    obtain ⟨hp, hi, hds, hpH, hn⟩ := hps x hx
    refine ⟨hp.prime, hi, fun y => ?_, ?_, hn⟩
    · have := Grp.nsmul_eq_zero (N := x.1 ^ x.2.1 + 1) c.ds hds y
      rw [add_smul, one_smul] at this
      exact eq_neg_of_add_eq_zero_left this
    · rw [Grp.card_eq, Ne, ZMod.natCast_eq_zero_iff]
      exact hpH
  refine not_hasSDS_of_compositeModulus _ (quot_surjective r.ms c.ds hdv) hcard
    (Grp.exists_ne_zero c.ds hH1) hk hL hpw (s := c.s) ?_ ?_
  · rw [hs, Grp.card_eq, ← Nat.cast_mul, Nat.div_mul_cancel hprod]
  · intro s' hs' t ht
    obtain ⟨ht0, htq⟩ := Finset.mem_Ico.1 ht
    have htn : t.toNat < (modulusProd c.ps).toNat :=
      (Int.toNat_lt_toNat (lt_of_le_of_lt ht0 htq)).2 htq
    have := hfail s' hs' t.toNat (List.mem_range.2 htn)
    rw [Int.toNat_of_nonneg ht0] at this
    rwa [Grp.card_eq]

end SignedDifferenceSets
