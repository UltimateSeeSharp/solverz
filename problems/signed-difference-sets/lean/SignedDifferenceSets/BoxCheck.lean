module

public import SignedDifferenceSets.Box
public import SignedDifferenceSets.SelfConjugacyCheck

/-!
# Checking C14 on the table's rows

As `SelfConjugacyCheck`, with the box test: a row with a certificate is killed when
`ScCert.Valid` holds, `s² = k + λ(v − 1)` and every sign `±s` and residue fails `BoxOk`.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- C14 kills the row: every sign and residue fails the box test. -/
def ScCert.BoxKills (r : Row) (c : ScCert) : Prop :=
  c.Valid r ∧ c.s ^ 2 = r.k + r.lam * ((r.ms.prod : ℤ) - 1) ∧
    ∀ s' ∈ [c.s, -c.s], ∀ t ∈ List.range (c.p ^ c.j),
      ¬ BoxOk c.ds.prod ((c.p : ℤ) ^ c.j) s'
        (r.k + r.lam * (((r.ms.prod / c.ds.prod : ℕ) : ℤ) - 1)) t
        ((r.ms.prod / c.ds.prod : ℕ) : ℤ)

instance (r : Row) (c : ScCert) : Decidable (c.BoxKills r) := by
  unfold ScCert.BoxKills ScCert.Valid; infer_instance

/-- A row C14 kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem ScCert.not_hasSDS_of_boxKills {r : Row} {c : ScCert} (h : c.BoxKills r)
    (inst : Fintype (Grp r.ms)) : ¬ @HasSDS (Grp r.ms) _ inst r.k r.lam := by
  obtain ⟨⟨hp, hi, hms, hdv, hds, hpH, hH1, hn, hk⟩, hs, hfail⟩ := h
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
  refine not_hasSDS_of_box _ (quot_surjective r.ms c.ds hdv) hcard hi hc hH
    (Grp.exists_ne_zero c.ds hH1) hn hk (s := c.s) ?_ ?_
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
