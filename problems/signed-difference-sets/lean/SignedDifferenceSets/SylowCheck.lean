module

public import SignedDifferenceSets.SylowTrace
public import SignedDifferenceSets.SelfConjugacyCheck
public import SignedDifferenceSets.MaRows.Polys

/-!
# Checking C22 on the table's rows

A row with a certificate (prime `p`, `r = p^(J−1)`, `e`, `q`, `t`, sign sum `s`, Sylow quotient
`Grp ds` by `dᵢ ∣ mᵢ`) dies when `SyCert.Kills` holds: plain arithmetic, `p^min(t, q+1) ∤ s`, and
`(p, r)` in `MaRows.maPairs`, whose cyclotomic facts are certified. `SyCert.not_hasSDS` applies
`not_hasSDS_of_sylow`; rows are checked in chunks by `decide +kernel`.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- A C22 certificate: `p`, `r = p^(J−1)`, `e` with `p^e ∣ k − λ`, `q`, `t` with `|H| = p^t`, the
sign sum `s` and the quotient `Grp ds`. -/
structure SyCert where
  p : ℕ
  r : ℕ
  e : ℕ
  q : ℕ
  t : ℕ
  s : ℤ
  ds : List ℕ
  deriving DecidableEq

/-- `SylowTrace.PPowers`, decidably: every factor is a positive power of `p` dividing `N`. -/
def PPowersB (p N : ℕ) (ds : List ℕ) : Prop := ∀ d ∈ ds, 0 < d ∧ d ∣ N ∧ p ^ Nat.log p d = d

instance (p N : ℕ) (ds : List ℕ) : Decidable (PPowersB p N ds) := by
  unfold PPowersB; infer_instance

theorem PPowersB.pPowers {p N : ℕ} {ds : List ℕ} (h : PPowersB p N ds) :
    SylowTrace.PPowers p N ds :=
  fun d hd => ⟨(h d hd).1, (h d hd).2.1, Nat.log p d, (h d hd).2.2.symm⟩

/-- C22 kills the row. -/
def SyCert.Kills (r : Row) (c : SyCert) : Prop :=
  IsPrimeTD c.p ∧ 0 < c.r ∧ (∀ m ∈ r.ms, 0 < m) ∧ Dvds c.ds r.ms ∧
    PPowersB c.p (c.r * c.p) c.ds ∧ (c.p : ℤ) ^ c.e ∣ (r.k : ℤ) - r.lam ∧
    2 * (c.q * ((c.p - 1) * c.r) + 1) ≤ c.e * ((c.p - 1) * c.r) ∧ c.ds.prod = c.p ^ c.t ∧
    c.s ^ 2 = r.k + r.lam * ((r.ms.prod : ℤ) - 1) ∧ ¬ (c.p : ℤ) ^ min c.t (c.q + 1) ∣ c.s ∧
    (c.p, c.r) ∈ MaRows.maPairs

instance SyCert.instDecidableKills (r : Row) (c : SyCert) : Decidable (c.Kills r) := by
  unfold SyCert.Kills; infer_instance

/-- A row C22 kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem SyCert.not_hasSDS {r : Row} {c : SyCert} (h : c.Kills r) (inst : Fintype (Grp r.ms)) :
    ¬ @HasSDS (Grp r.ms) _ inst r.k r.lam := by
  obtain ⟨hp, hr, hms, hdv, hpp, hn, hq, ht, hs, hkill, hpair⟩ := h
  have : Fact c.p.Prime := ⟨hp.prime⟩
  have : NeZero (c.r * c.p) := ⟨Nat.mul_ne_zero hr.ne' hp.prime.ne_zero⟩
  let _ : Fintype (Grp c.ds) := Grp.fintype c.ds (Dvds.pos _ _ hdv hms)
  have hprod := Dvds.prod_dvd _ _ hdv
  have hcard : Fintype.card (Grp r.ms) = (r.ms.prod / c.ds.prod) * Fintype.card (Grp c.ds) := by
    rw [Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  refine not_hasSDS_of_sylow c.ds hpp.pPowers (quot r.ms c.ds hdv) (quot_surjective r.ms c.ds hdv)
    hcard hn hq (t := c.t) (by rw [Grp.card_eq, ht]) (s := c.s) ?_ hkill
    (MaRows.cycloFacts_of_mem_maPairs hpair)
  rw [hs, Grp.card_eq, ← Nat.cast_mul, Nat.div_mul_cancel hprod]

end SignedDifferenceSets
