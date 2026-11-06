module

public import SignedDifferenceSets.MarkedCounts
public import SignedDifferenceSets.SelfConjugacyCheck

/-!
# Checking C7 on the table's rows

As `BoxCheck`, with weights: a row with a certificate (C5's data `ScCert` and a list of weights)
is killed when `ScCert.Valid` holds, `s² = k + λ(v − 1)`, and every sign `±s` and residue
fails `BoxOk` or has a listed weight passing the lower or upper test, run over the list of the
values `x ∈ [−c, c]` with `x ≡ t₀ (mod q)`. `McCert.not_hasSDS` turns a kill into `¬ HasSDS`.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- The values `x ∈ [−c, c]` with `x ≡ t₀ (mod q)`. -/
def classVals (q t0 c : ℤ) : List ℤ :=
  ((List.range (2 * c + 1).toNat).map fun n : ℕ => (n : ℤ) - c).filter
    fun x => (x - t0) % q = 0

theorem mem_classVals {q t0 c x : ℤ} (hx : |x| ≤ c) (hq : q ∣ x - t0) :
    x ∈ classVals q t0 c := by
  have hx' := abs_le.1 hx
  unfold classVals
  rw [List.mem_filter, List.mem_map]
  refine ⟨⟨(x + c).toNat, List.mem_range.2 ?_, ?_⟩, decide_eq_true (Int.emod_eq_zero_of_dvd hq)⟩
  · omega
  · omega

/-- `Weights.Lower` with the class's values listed. -/
def Weights.LowerChk (w : Weights) (N q s' Q t0 c k : ℤ) : Prop :=
  0 ≤ w.d ∧ (∀ x ∈ classVals q t0 c, w.eval x ≤ w.d * |x|) ∧ w.d * k < w.total N s' Q

/-- `Weights.Upper` with the class's values listed. -/
def Weights.UpperChk (w : Weights) (N q s' Q t0 c k : ℤ) : Prop :=
  0 ≤ w.d ∧ (∀ x ∈ classVals q t0 c, w.d * maxMarked c x ≤ w.eval x) ∧
    w.total N s' Q < w.d * k

instance (w : Weights) (N q s' Q t0 c k : ℤ) : Decidable (w.LowerChk N q s' Q t0 c k) := by
  unfold Weights.LowerChk; infer_instance

instance (w : Weights) (N q s' Q t0 c k : ℤ) : Decidable (w.UpperChk N q s' Q t0 c k) := by
  unfold Weights.UpperChk; infer_instance

theorem Weights.LowerChk.lower {w : Weights} {N q s' Q t0 c k : ℤ}
    (h : w.LowerChk N q s' Q t0 c k) : w.Lower N q s' Q t0 c k :=
  ⟨h.1, fun x hx hq => h.2.1 x (mem_classVals hx hq), h.2.2⟩

theorem Weights.UpperChk.upper {w : Weights} {N q s' Q t0 c k : ℤ}
    (h : w.UpperChk N q s' Q t0 c k) : w.Upper N q s' Q t0 c k :=
  ⟨h.1, fun x hx hq => h.2.1 x (mem_classVals hx hq), h.2.2⟩

/-- A certificate for C7: C5's data and weights for the signs and residues C14 leaves. -/
structure McCert where
  sc : ScCert
  ws : List Weights
  deriving DecidableEq

/-- C7 kills the row: every sign and residue fails C14's box test or has listed weights. -/
def McCert.Kills (r : Row) (c : McCert) : Prop :=
  c.sc.Valid r ∧ c.sc.s ^ 2 = r.k + r.lam * ((r.ms.prod : ℤ) - 1) ∧
    ∀ s' ∈ [c.sc.s, -c.sc.s], ∀ t ∈ List.range (c.sc.p ^ c.sc.j),
      ¬ BoxOk c.sc.ds.prod ((c.sc.p : ℤ) ^ c.sc.j) s'
          (r.k + r.lam * (((r.ms.prod / c.sc.ds.prod : ℕ) : ℤ) - 1)) t
          ((r.ms.prod / c.sc.ds.prod : ℕ) : ℤ) ∨
        ∃ w ∈ c.ws,
          w.LowerChk c.sc.ds.prod ((c.sc.p : ℤ) ^ c.sc.j) s'
              (r.k + r.lam * (((r.ms.prod / c.sc.ds.prod : ℕ) : ℤ) - 1)) t
              ((r.ms.prod / c.sc.ds.prod : ℕ) : ℤ) r.k ∨
            w.UpperChk c.sc.ds.prod ((c.sc.p : ℤ) ^ c.sc.j) s'
              (r.k + r.lam * (((r.ms.prod / c.sc.ds.prod : ℕ) : ℤ) - 1)) t
              ((r.ms.prod / c.sc.ds.prod : ℕ) : ℤ) r.k

instance McCert.instDecidableKills (r : Row) (c : McCert) : Decidable (c.Kills r) := by
  unfold McCert.Kills ScCert.Valid; infer_instance

/-- A row C7 kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem McCert.not_hasSDS {r : Row} {c : McCert} (h : c.Kills r)
    (inst : Fintype (Grp r.ms)) : ¬ @HasSDS (Grp r.ms) _ inst r.k r.lam := by
  obtain ⟨⟨hp, hi, hms, hdv, hds, hpH, hH1, hn, hk⟩, hs, hfail⟩ := h
  have : Fact c.sc.p.Prime := ⟨hp.prime⟩
  let _ : Fintype (Grp c.sc.ds) := Grp.fintype c.sc.ds (Dvds.pos _ _ hdv hms)
  have hprod := Dvds.prod_dvd _ _ hdv
  have hcard : Fintype.card (Grp r.ms) =
      (r.ms.prod / c.sc.ds.prod) * Fintype.card (Grp c.sc.ds) := by
    rw [Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hc (x : Grp c.sc.ds) : c.sc.p ^ c.sc.i • x = -x := by
    have := Grp.nsmul_eq_zero (N := c.sc.p ^ c.sc.i + 1) c.sc.ds hds x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  have hH : (Fintype.card (Grp c.sc.ds) : ZMod c.sc.p) ≠ 0 := by
    rw [Grp.card_eq, Ne, ZMod.natCast_eq_zero_iff]
    exact hpH
  refine not_hasSDS_of_marked _ (quot_surjective r.ms c.sc.ds hdv) hcard hi hc hH
    (Grp.exists_ne_zero c.sc.ds hH1) hn hk (s := c.sc.s) ?_ ?_
  · rw [hs, Grp.card_eq, ← Nat.cast_mul, Nat.div_mul_cancel hprod]
  · intro s' hs' t ht
    obtain ⟨ht0, htq⟩ := Finset.mem_Ico.1 ht
    have htn : t.toNat < c.sc.p ^ c.sc.j := by
      have : (t.toNat : ℤ) < (c.sc.p : ℤ) ^ c.sc.j := by
        rw [Int.toNat_of_nonneg ht0]; exact htq
      exact_mod_cast this
    have := hfail s' hs' t.toNat (List.mem_range.2 htn)
    rw [Int.toNat_of_nonneg ht0] at this
    rw [Grp.card_eq]
    rcases this with h1 | ⟨w, -, h2 | h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨w, Or.inl h2.lower⟩
    · exact Or.inr ⟨w, Or.inr h2.upper⟩

end SignedDifferenceSets
