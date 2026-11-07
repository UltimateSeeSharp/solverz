import SignedDifferenceSets.SelfConjugacyCheck

/-! Refuter: Box.lean and BoxCheck.lean bodies verbatim (not yet built), a sample of BoxRows. -/

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

namespace SignedDifferenceSets.BoxRows
def sample : List (Row × ScCert) := [
  (⟨194, [37], 36, 8⟩, ⟨2, 1, 18, [37], 18⟩),
  (⟨290, [3, 15], 37, 21⟩, ⟨2, 2, 1, [3, 3], 31⟩),
  (⟨514, [56], 44, 8⟩, ⟨3, 1, 3, [28], 22⟩),
  (⟨523, [57], 32, 4⟩, ⟨2, 1, 9, [57], 16⟩),
  (⟨581, [60], 53, 4⟩, ⟨7, 1, 2, [10], 17⟩),
  (⟨726, [2, 2, 2, 8], 46, 10⟩, ⟨3, 1, 1, [2, 2, 2, 4], 26⟩),
  (⟨729, [2, 4, 8], 46, 10⟩, ⟨3, 1, 1, [2, 4, 4], 26⟩),
  (⟨748, [2, 2, 2, 8], 58, 22⟩, ⟨3, 1, 1, [1, 2, 2, 4], 38⟩),
  (⟨750, [2, 2, 16], 58, 22⟩, ⟨3, 1, 1, [2, 2, 4], 38⟩),
  (⟨751, [2, 4, 8], 58, 22⟩, ⟨3, 1, 1, [1, 4, 4], 38⟩),
  (⟨754, [4, 16], 58, 22⟩, ⟨3, 1, 1, [4, 4], 38⟩),
  (⟨755, [8, 8], 58, 22⟩, ⟨3, 1, 1, [4, 4], 38⟩),
  (⟨1188, [2, 2, 20], 50, 14⟩, ⟨3, 1, 2, [2, 2, 10], 34⟩),
  (⟨1203, [2, 2, 20], 62, 26⟩, ⟨3, 1, 2, [1, 2, 10], 46⟩),
  (⟨1204, [2, 40], 62, 26⟩, ⟨3, 1, 2, [2, 10], 46⟩),
  (⟨24920, [2, 152], 232, 88⟩, ⟨3, 1, 9, [1, 76], 164⟩),
  (⟨24922, [304], 232, 88⟩, ⟨3, 1, 9, [76], 164⟩),
  (⟨25054, [305], 137, 56⟩, ⟨3, 2, 5, [61], 131⟩),
  (⟨25082, [305], 180, 99⟩, ⟨3, 2, 5, [61], 174⟩),
  (⟨25145, [305], 292, 48⟩, ⟨2, 1, 30, [305], 122⟩),
  (⟨25169, [3, 102], 121, 40⟩, ⟨3, 2, 8, [1, 34], 111⟩),
  (⟨25170, [306], 121, 40⟩, ⟨3, 2, 8, [34], 111⟩),
  (⟨25177, [3, 102], 141, 20⟩, ⟨11, 1, 8, [1, 34], 79⟩),
  (⟨25178, [306], 141, 20⟩, ⟨11, 1, 8, [34], 79⟩),
  (⟨25217, [3, 102], 229, 148⟩, ⟨3, 2, 8, [1, 17], 213⟩),
  (⟨68917, [494], 376, 120⟩, ⟨2, 4, 9, [19], 244⟩),
  (⟨68954, [494], 457, 408⟩, ⟨7, 1, 6, [13], 449⟩),
  (⟨68963, [494], 468, 432⟩, ⟨3, 1, 9, [19], 462⟩),
  (⟨69413, [3, 165], 480, 336⟩, ⟨2, 2, 5, [1, 33], 408⟩),
  (⟨69414, [495], 480, 336⟩, ⟨2, 2, 5, [33], 408⟩),
  (⟨69565, [496], 229, 60⟩, ⟨13, 1, 15, [62], 173⟩),
  (⟨69603, [2, 248], 256, 112⟩, ⟨3, 1, 15, [1, 124], 236⟩),
  (⟨69605, [496], 256, 112⟩, ⟨3, 1, 15, [124], 236⟩),
  (⟨69638, [2, 248], 280, 136⟩, ⟨3, 1, 15, [1, 124], 260⟩),
  (⟨69640, [496], 280, 136⟩, ⟨3, 1, 15, [124], 260⟩),
  (⟨69815, [496], 379, 210⟩, ⟨13, 1, 15, [31], 323⟩),
  (⟨69988, [2, 248], 495, 54⟩, ⟨3, 1, 15, [2, 124], 165⟩),
  (⟨70001, [497], 128, 7⟩, ⟨11, 1, 35, [71], 60⟩),
  (⟨70470, [499], 424, 12⟩, ⟨2, 1, 83, [499], 80⟩),
  (⟨70505, [499], 456, 28⟩, ⟨2, 1, 83, [499], 120⟩)
]

set_option maxRecDepth 100000 in
theorem sample_kills : ∀ x ∈ sample, x.2.BoxKills x.1 := by decide +kernel

-- N194 SDS(37,36,8,[37]) C14 2 1 18 37 18
example : ¬ HasSDS (ZMod 37) 36 8 :=
  ScCert.not_hasSDS_of_boxKills (r := ⟨194, [37], 36, 8⟩) (c := ⟨2, 1, 18, [37], 18⟩)
    (by decide +kernel) _

set_option pp.funBinderTypes true in
#check @SignedDifferenceSets.not_hasSDS_of_box
#print axioms sample_kills
#print axioms SignedDifferenceSets.not_hasSDS_of_box
#print axioms SignedDifferenceSets.ScCert.not_hasSDS_of_boxKills
end SignedDifferenceSets.BoxRows
