module

public import SignedDifferenceSets.Moments
public import SignedDifferenceSets.Rows

/-!
# Checking C5 and C6 on the table's rows

A row (`id`, group `Grp ms`, `k`, `λ`) with a certificate (prime `p`, exponents `j` and `i`,
quotient `Grp ds` by `dᵢ ∣ mᵢ`, sign sum `s`) is killed when the shared hypotheses hold
(`ScCert.Valid`, plain arithmetic) and either C5's bound `2c < p^j` holds or C6's moments test
fails for `±s` and every residue (`ScCert.Kills`). `ScCert.not_hasSDS` turns a kill into
`¬ HasSDS`; the rows are checked in chunks by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- A row of the table: its Instance number, group factors, `k` and `λ`. -/
structure Row where
  id : ℕ
  ms : List ℕ
  k : ℕ
  lam : ℤ
  deriving DecidableEq

/-- A certificate for C5 or C6: prime `p`, `p^(2j) ∣ k − λ`, `p^i ≡ −1` on `Grp ds`, and the
sign sum `s` (C1) for the moments test. -/
structure ScCert where
  p : ℕ
  j : ℕ
  i : ℕ
  ds : List ℕ
  s : ℤ
  deriving DecidableEq

/-- Primality by trial division, which the kernel evaluates directly. -/
def IsPrimeTD (p : ℕ) : Prop := 2 ≤ p ∧ ∀ d ∈ List.range p, 2 ≤ d → p % d ≠ 0

instance (p : ℕ) : Decidable (IsPrimeTD p) := by unfold IsPrimeTD; infer_instance

theorem IsPrimeTD.prime {p : ℕ} (h : IsPrimeTD p) : p.Prime :=
  Nat.prime_def_lt'.2 ⟨h.1, fun m hm hmp hdvd =>
    h.2 m (List.mem_range.2 hmp) hm (Nat.mod_eq_zero_of_dvd hdvd)⟩

/-- The hypotheses C5 and C6 share, as arithmetic on the row and certificate. -/
def ScCert.Valid (r : Row) (c : ScCert) : Prop :=
  IsPrimeTD c.p ∧ 0 < c.i ∧ (∀ m ∈ r.ms, 0 < m) ∧ Dvds c.ds r.ms ∧
    (∀ d ∈ c.ds, d ∣ c.p ^ c.i + 1) ∧ ¬ c.p ∣ c.ds.prod ∧ 1 < c.ds.prod ∧
    (c.p : ℤ) ^ (2 * c.j) ∣ r.k - r.lam ∧ (r.k : ℤ) ≠ r.lam

/-- C5's bound holds, or C6's moments test fails for both signs and every residue. -/
def ScCert.Kills (r : Row) (c : ScCert) : Prop :=
  c.Valid r ∧ (2 * (r.ms.prod / c.ds.prod) < c.p ^ c.j ∨
    (c.s ^ 2 = r.k + r.lam * ((r.ms.prod : ℤ) - 1) ∧
      ∀ s' ∈ [c.s, -c.s], ∀ t ∈ List.range (c.p ^ c.j),
        ¬ MomentsOk c.ds.prod ((c.p : ℤ) ^ c.j) s'
          (r.k + r.lam * (((r.ms.prod / c.ds.prod : ℕ) : ℤ) - 1)) t))

instance (r : Row) (c : ScCert) : Decidable (c.Kills r) := by
  unfold ScCert.Kills ScCert.Valid; infer_instance

theorem Dvds.pos : (ds ms : List ℕ) → Dvds ds ms → (∀ m ∈ ms, 0 < m) → ∀ d ∈ ds, 0 < d
  | [], [], _, _ => by simp
  | d :: ds, m :: ms, h, hm => by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Nat.pos_of_dvd_of_pos h.1 (hm m List.mem_cons_self)
    · exact Dvds.pos ds ms h.2 (fun y hy => hm y (List.mem_cons_of_mem _ hy)) x hx
  | [], _ :: _, h, _ => False.elim h
  | _ :: _, [], h, _ => False.elim h

theorem Dvds.prod_dvd : (ds ms : List ℕ) → Dvds ds ms → ds.prod ∣ ms.prod
  | [], [], _ => dvd_rfl
  | d :: ds, m :: ms, h => by
    rw [List.prod_cons, List.prod_cons]
    exact mul_dvd_mul h.1 (Dvds.prod_dvd ds ms h.2)
  | [], _ :: _, h => False.elim h
  | _ :: _, [], h => False.elim h

/-- A killed row has no SDS, whatever `Fintype` instance its group carries. -/
theorem ScCert.not_hasSDS {r : Row} {c : ScCert} (h : c.Kills r) (inst : Fintype (Grp r.ms)) :
    ¬ @HasSDS (Grp r.ms) _ inst r.k r.lam := by
  obtain ⟨⟨hp, hi, hms, hdv, hds, hpH, hH1, hn, hk⟩, hkill⟩ := h
  have : Fact c.p.Prime := ⟨hp.prime⟩
  let _ : Fintype (Grp c.ds) := Grp.fintype c.ds (Dvds.pos _ _ hdv hms)
  have hprod := Dvds.prod_dvd _ _ hdv
  have hcard : Fintype.card (Grp r.ms) =
      (r.ms.prod / c.ds.prod) * Fintype.card (Grp c.ds) := by
    rw [Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hc (x : Grp c.ds) : c.p ^ c.i • x = -x := by
    have := Grp.nsmul_eq_zero (N := c.p ^ c.i + 1) c.ds hds x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  have hH : (Fintype.card (Grp c.ds) : ZMod c.p) ≠ 0 := by
    rw [Grp.card_eq, Ne, ZMod.natCast_eq_zero_iff]
    exact hpH
  have hH1' := Grp.exists_ne_zero c.ds hH1
  have hφ := quot_surjective r.ms c.ds hdv
  rcases hkill with h2 | ⟨hs, hfail⟩
  · exact not_hasSDS_of_selfConj _ hφ hcard hi hc hH hH1' hn hk h2
  · refine not_hasSDS_of_moments _ hφ hcard hi hc hH hH1' hn hk (s := c.s) ?_ ?_
    · rw [hs, Grp.card_eq, ← Nat.cast_mul, Nat.div_mul_cancel hprod]
    · intro s' hs' t ht
      obtain ⟨ht0, htq⟩ := Finset.mem_Ico.1 ht
      have htn : t.toNat < c.p ^ c.j := by
        have : (t.toNat : ℤ) < (c.p : ℤ) ^ c.j := by rw [Int.toNat_of_nonneg ht0]; exact htq
        exact_mod_cast this
      have := hfail s' hs' t.toNat (List.mem_range.2 htn)
      rw [Int.toNat_of_nonneg ht0] at this
      rwa [Grp.card_eq]

end SignedDifferenceSets
