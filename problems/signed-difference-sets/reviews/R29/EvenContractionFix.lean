module

public import SignedDifferenceSets.ContractionCheck
public import SignedDifferenceSets.CosetSearch
public import SignedDifferenceSets.MaDescentFull

/-!
# The even contraction (C28, C26 at any `c`)

On a quotient `ZMod (2r) × K` (fibres of size `c`) with `2` self-conjugate on `K` and `4 ∣ n`,
Ma's step (`Ma.dvd_contract_sub`, `b = 1`) makes the coset sums `W` on `L = ZMod r × K` even. So
`Z = W / 2` has `|Z| ≤ c`, `Σ Z² = Q`, `4 Q = k + λ(2c − 1)`, autocorrelation `t`, `2 t = λ c`,
`Σ Z = ±s/2` and `Σ |Z| ≤ k/2`, `Σ |Z| ≡ s/2 (mod 2)`; when `noVector` rules every such `Z` out,
there is no SDS (`not_hasSDS_of_evenContraction`). `EvenCert` checks it on a row
(`EvenCert.Ok`, and `EvenCert.search`, which a row may split with `onGrp_of` and `noVector_of_top`).
-/

@[expose] public section

namespace SignedDifferenceSets

section Group

variable {H : Type*} [AddCommGroup H] [Fintype H]

/-- The demands `noVector n add c Q t K s` makes of a vector `b` (besides `Σ b = s`). -/
structure VecDemands (c : ℕ) (Q t K : ℤ) (b : H → ℤ) : Prop where
  bound : ∀ h, |b h| ≤ c
  sq : ∑ h, b h * b h = Q
  corr : ∀ g, g ≠ 0 → ∑ h, b h * b (h + g) = t
  abs : ∑ h, |b h| ≤ K
  parity : (K - ∑ h, |b h|) % 2 = 0

variable {c : ℕ} {Q t K : ℤ} {b : H → ℤ}

theorem VecDemands.neg (hb : VecDemands c Q t K b) : VecDemands c Q t K (fun h => -b h) where
  bound h := by rw [abs_neg]; exact hb.bound h
  sq := by simpa only [neg_mul_neg] using hb.sq
  corr g hg := by simpa only [neg_mul_neg] using hb.corr g hg
  abs := by simpa only [abs_neg] using hb.abs
  parity := by simpa only [abs_neg] using hb.parity

theorem VecDemands.translate (hb : VecDemands c Q t K b) (h₀ : H) :
    VecDemands c Q t K (fun h => b (h + h₀)) where
  bound h := hb.bound _
  sq := by rw [← hb.sq]; exact Fintype.sum_equiv (Equiv.addRight h₀) _ _ fun _ => rfl
  corr g hg := by
    rw [← hb.corr g hg]
    simp only [add_right_comm _ g h₀]
    exact Fintype.sum_equiv (Equiv.addRight h₀) _ (fun u => b u * b (u + g)) fun _ => rfl
  abs := by
    rw [Fintype.sum_equiv (Equiv.addRight h₀) (fun h => |b (h + h₀)|) (fun u => |b u|)
      fun _ => rfl]; exact hb.abs
  parity := by
    rw [Fintype.sum_equiv (Equiv.addRight h₀) (fun h => |b (h + h₀)|) (fun u => |b u|)
      fun _ => rfl]; exact hb.parity

variable [Indexed H]

/-- A vector meeting the demands, `Σ b = s` and `|b 0|` largest, contradicts `noVector`. -/
theorem false_of_noVectorQ {s : ℤ}
    (hn : noVector (Indexed.size H) (Indexed.addIdx H) c Q t K s = true)
    (hb : VecDemands c Q t K b) (hmax : ∀ h, |b h| ≤ |b 0|) (hs : ∑ h, b h = s) : False := by
  set n := Indexed.size H
  set e : H ≃ Fin n := Indexed.equiv
  have hpos : 0 < n := (e 0).pos
  have he0 : e.symm ⟨0, hpos⟩ = 0 := e.symm_apply_eq.2 (Fin.ext Indexed.equiv_zero.symm)
  set F : Fin n → ℤ := fun i => b (e.symm i)
  have hsum (f : ℤ → ℤ) : ((List.ofFn F).map f).sum = ∑ h, f (b h) := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact e.symm.sum_comp (fun h => f (b h))
  have hmem : ∀ y ∈ List.ofFn F, ∃ h, b h = y := by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact ⟨_, rfl⟩
  have hne : List.ofFn F ≠ [] := by
    intro h
    have := List.length_ofFn (f := F)
    rw [h] at this
    simp at this
    omega
  obtain ⟨x, w, hL⟩ := List.exists_cons_of_ne_nil hne
  have hx : x = b 0 := by
    have := getD_ofFn F hpos
    rw [hL] at this
    simpa [F, he0] using this
  have hw : ∀ y ∈ w, ∃ h, b h = y := fun y hy => hmem y (hL ▸ List.mem_cons_of_mem x hy)
  refine noVector_sound hn x w (by rw [← hL, List.length_ofFn]) (hx ▸ hb.bound 0)
    (fun y hy => ?_) (fun y hy => ?_) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hx ▸ hmax h
  · obtain ⟨h, rfl⟩ := hw y hy
    exact hb.bound h
  · rw [← hL, ← hs]
    simpa using hsum id
  · rw [← hL, ← hb.sq]
    exact hsum fun y => y * y
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.abs
  · rw [← hL]
    simp only [absSum]
    rw [hsum fun y => |y|]
    exact hb.parity
  · rw [← hL, shiftsOK, allTo_iff]
    intro g hg
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · simp
    set gH := e.symm ⟨g, hg⟩
    have hgH : (e gH : ℕ) = g := by simp [gH]
    have hgH0 : gH ≠ 0 := by
      intro h0
      have := hgH
      rw [h0, Indexed.equiv_zero] at this
      omega
    simp only [Bool.or_eq_true, beq_iff_eq]
    right
    rw [← hb.corr gH hgH0, sumTo_eq, ← sum_equiv (G := H)]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← hgH, ← Indexed.equiv_add, getD_ofFn F (e u).isLt, getD_ofFn F (e (u + gH)).isLt]
    simp [F]

/-- No vector meeting the demands with `Σ b = ±s` when `noVector` holds at `s`. -/
theorem false_of_noVectorQ_sum {s : ℤ}
    (hn : noVector (Indexed.size H) (Indexed.addIdx H) c Q t K s = true)
    (hb : VecDemands c Q t K b) (hs : ∑ h, b h = s ∨ ∑ h, b h = -s) : False := by
  have key : ∀ b' : H → ℤ, VecDemands c Q t K b' → ∑ h, b' h = s → False := by
    intro b' hb' hbs
    obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun h => |b' h|)
      Finset.univ_nonempty
    refine false_of_noVectorQ hn (hb'.translate h₀) (fun h => ?_) ?_
    · simpa using hmax (h + h₀) (Finset.mem_univ _)
    · rw [← hbs]
      exact Fintype.sum_equiv (Equiv.addRight h₀) _ b' fun _ => rfl
  rcases hs with h1 | h1
  · exact key b hb h1
  · exact key _ hb.neg (by rw [Finset.sum_neg_distrib, h1, neg_neg])

end Group

open Ma

/-- C28: no SDS on `G` when `noVector` rules out the halved coset sums on `ZMod r × K`. -/
theorem not_hasSDS_of_evenContraction {G K : Type} [AddCommGroup G] [Fintype G]
    [AddCommGroup K] [Fintype K] {r i c k : ℕ} {lam : ℤ} [NeZero (r * 2)] [NeZero r]
    [Indexed (ZMod r × K)] {φ : G →+ ZMod (r * 2) × K} (hφ : Function.Surjective φ)
    (hcard : Fintype.card G = c * Fintype.card (ZMod (r * 2) × K)) (hr : 0 < r) (hi : 0 < i)
    (hc : ∀ x : K, 2 ^ i • x = -x) (hn : (2 : ℤ) ^ 2 ∣ (k : ℤ) - lam) (hcert : CycloFacts 2 r)
    {s s₂ Q t K' : ℤ} (hs : s * s = k + lam * ((Fintype.card G : ℤ) - 1)) (hs₂ : s = 2 * s₂)
    (hQ : 4 * Q = k + lam * (2 * c - 1)) (ht : 2 * t = lam * c) (hK₁ : (K' - s₂) % 2 = 0)
    (hK₂ : (k : ℤ) < 2 * K' + 4)
    (hnv : noVector (Indexed.size (ZMod r × K)) (Indexed.addIdx (ZMod r × K)) c Q t K' s₂ = true) :
    ¬ HasSDS G k lam := by
  classical
  rintro ⟨D, hD⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ : ZMod (r * 2) × K →+ ZMod r × K :=
    ((ZMod.castHom (dvd_mul_right r 2) (ZMod r)).toAddMonoidHom).prodMap (AddMonoidHom.id K)
    with hψdef
  have hψ : Function.Surjective ψ := by
    rintro ⟨a, b⟩
    obtain ⟨a', ha'⟩ := ZMod.ringHom_surjective (ZMod.castHom (dvd_mul_right r 2) (ZMod r)) a
    exact ⟨(a', b), by simp [hψdef, ha']⟩
  set u : ZMod (r * 2) × K := ((r : ZMod (r * 2)), 0) with hu
  have hrv : ((r : ℕ) : ZMod (r * 2)).val = r :=
    ZMod.val_cast_of_lt (lt_mul_of_one_lt_right hr one_lt_two)
  have hu0 : u ≠ 0 := by
    intro h
    have := congrArg (fun z => (Prod.fst z).val) h
    simp only [hu, Prod.fst_zero, ZMod.val_zero, hrv] at this
    omega
  have hψu : ψ u = 0 := by
    simp [hψdef, hu]
  set χ := ψ.comp φ with hχdef
  have hχ : Function.Surjective χ := hψ.comp hφ
  have hcardH : Fintype.card (ZMod (r * 2) × K) = 2 * Fintype.card (ZMod r × K) := by
    rw [Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card]
    ring
  have hcard2 : Fintype.card G = (2 * c) * Fintype.card (ZMod r × K) := by
    rw [hcard, hcardH]; ring
  set Y := contract φ D with hYdef
  set W := contract χ D with hWdef
  have hfibψ : ∀ h : ZMod (r * 2) × K,
      Finset.univ.filter (fun h' => ψ h' = ψ h) = {h, h + u} := by
    intro h
    symm
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [map_add, hψu]
    · have h2 := card_fibre_eq hψ hcardH (ψ h)
      rw [fibre] at h2
      rw [h2, Finset.card_pair (fun e => hu0 (by simpa using e.symm))]
  have hW : ∀ h, W (ψ h) = Y h + Y (h + u) := by
    intro h
    rw [hWdef, hχdef, contract_comp, hfibψ h,
      Finset.sum_pair (fun e => hu0 (by simpa using e.symm))]
  have hdiv : ∀ h, (2 : ℤ) ∣ Y (h + u) - Y h := by
    rintro ⟨x, kk⟩
    have := Ma.dvd_contract_sub (b := 1) (e := 2) hφ hcard hr hi hc hn (by norm_num) hcert hD x kk
    simpa [hu] using this
  have hWeven : ∀ y, (2 : ℤ) ∣ W y := by
    intro y
    obtain ⟨h, rfl⟩ := hψ y
    obtain ⟨q, hq⟩ := hdiv h
    exact ⟨Y h + q, by rw [hW h]; linarith⟩
  -- the halved coset sums
  set Z : ZMod r × K → ℤ := fun y => W y / 2 with hZdef
  have hZ : ∀ y, W y = 2 * Z y := fun y => (Int.mul_ediv_cancel' (hWeven y)).symm
  have hfib := card_fibre_eq hχ hcard2
  have hc1 : 1 ≤ 2 * c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have := (Fintype.card_pos : 0 < Fintype.card G)
      rw [hcard, h0, zero_mul] at this
      omega
    · omega
  have hsqW : ∑ y, W y * W y = k + lam * (((2 * c : ℕ) : ℤ) - 1) := by
    have h1 := hD.contract_sq χ
    rw [← hWdef, hfib 0, Nat.cast_sub hc1, Nat.cast_one] at h1
    exact h1
  have hcorrW : ∀ g, g ≠ 0 → ∑ y, W y * W (y + g) = lam * ((2 * c : ℕ) : ℤ) := fun g hg => by
    have h1 := hD.contract_autocorr χ g hg
    rw [← hWdef, hfib] at h1
    exact h1
  have habsW : ∑ y, |W y| ≤ k := hD.sum_abs_contract_le χ
  have hZsq : ∑ y, Z y * Z y = Q := by
    have h4 : 4 * ∑ y, Z y * Z y = 4 * Q := by
      rw [Finset.mul_sum, hQ]
      have : ∑ y, 4 * (Z y * Z y) = ∑ y, W y * W y :=
        Finset.sum_congr rfl fun y _ => by rw [hZ y]; ring
      rw [this, hsqW]
      push_cast
      ring
    linarith
  have hZcorr : ∀ g, g ≠ 0 → ∑ y, Z y * Z (y + g) = t := by
    intro g hg
    have h4 : 4 * ∑ y, Z y * Z (y + g) = 4 * t := by
      rw [Finset.mul_sum]
      have : ∑ y, 4 * (Z y * Z (y + g)) = ∑ y, W y * W (y + g) :=
        Finset.sum_congr rfl fun y _ => by rw [hZ y, hZ (y + g)]; ring
      rw [this, hcorrW g hg]
      push_cast
      linear_combination (-2 : ℤ) * ht
    linarith
  have hZabs2 : 2 * ∑ y, |Z y| ≤ k := by
    rw [Finset.mul_sum]
    calc ∑ y, 2 * |Z y| = ∑ y, |W y| :=
          Finset.sum_congr rfl fun y _ => by rw [hZ y, abs_mul]; norm_num
      _ ≤ k := habsW
  -- `Σ Z = ±s₂`
  have hH1 : 1 ≤ Fintype.card (ZMod r × K) := Fintype.card_pos
  have hsumsq : (∑ y, Z y) * (∑ y, Z y) = s₂ * s₂ := by
    have h4 : 4 * ((∑ y, Z y) * (∑ y, Z y)) = 4 * (s₂ * s₂) := by
      rw [sum_mul_sum_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
      simp only [add_zero]
      rw [hZsq, Finset.sum_congr rfl fun g hg => hZcorr g (Finset.ne_of_mem_erase hg),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        nsmul_eq_mul, Nat.cast_sub hH1]
      have hs' : 4 * (s₂ * s₂) = k + lam * ((Fintype.card G : ℤ) - 1) := by
        rw [← hs, hs₂]; ring
      rw [hs', hcard2]
      push_cast
      linear_combination hQ + 2 * (((Fintype.card (ZMod r × K) : ℤ)) - 1) * ht
    linarith
  have hsum : ∑ y, Z y = s₂ ∨ ∑ y, Z y = -s₂ := mul_self_eq_mul_self_iff.1 hsumsq
  -- `Σ |Z| ≡ Σ Z ≡ s₂ (mod 2)`
  have hpar : (∑ y, |Z y| - ∑ y, Z y) % 2 = 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Int.emod_eq_zero_of_dvd (Finset.dvd_sum fun y _ => ?_)
    rcases abs_choice (Z y) with h | h <;> rw [h]
    · simp
    · exact ⟨-Z y, by ring⟩
  have hparS : (∑ y, |Z y| - s₂) % 2 = 0 := by
    rcases hsum with h | h
    · rw [← h]; exact hpar
    · have : ∑ y, |Z y| - s₂ = (∑ y, |Z y| - ∑ y, Z y) - 2 * s₂ := by rw [h]; ring
      rw [this]; omega
  have habsK : ∑ y, |Z y| ≤ K' := by omega
  have hdem : VecDemands c Q t K' Z :=
    { bound := fun y => by
        have h1 := abs_contract_le χ D y
        rw [hfib] at h1
        have h2 : |W y| = 2 * |Z y| := by rw [hZ y, abs_mul]; norm_num
        have h3 : |W y| ≤ 2 * (c : ℤ) := by exact_mod_cast h1
        linarith
      sq := hZsq
      corr := hZcorr
      abs := habsK
      parity := by omega }
  exact false_of_noVectorQ_sum hnv hdem hsum

/-- A C28 certificate: as `DescentCert` (`r`, `i`, `s`, `ks`, forms `A`, preimages `P`) with the
bound `K` on `Σ |Z|`. -/
structure EvenCert where
  r : ℕ
  i : ℕ
  s : ℤ
  K : ℤ
  ks : List ℕ
  A : List (List ℕ)
  P : List (List ℕ)
  deriving DecidableEq

/-- `c = |G| / (2r |K|)`. -/
def EvenCert.c (w : Row) (e : EvenCert) : ℕ := w.ms.prod / (e.r * 2 * e.ks.prod)

/-- C28's hypotheses on the row (all but the search). -/
def EvenCert.Ok (w : Row) (e : EvenCert) : Prop :=
  0 < e.r ∧ 0 < e.i ∧ (∀ m ∈ w.ms, 0 < m) ∧ e.ks ≠ [] ∧ (∀ d ∈ e.ks, d ∣ 2 ^ e.i + 1) ∧
    MapOk w.ms (e.r * 2 :: e.ks) e.A ∧ SurjCert w.ms (e.r * 2 :: e.ks) e.A e.P ∧
    e.r * 2 * e.ks.prod ∣ w.ms.prod ∧ (2 : ℤ) ^ 2 ∣ (w.k : ℤ) - w.lam ∧
    e.s * e.s = w.k + w.lam * ((w.ms.prod : ℤ) - 1) ∧ e.s % 2 = 0 ∧
    (w.k + w.lam * (2 * (e.c w : ℤ) - 1)) % 4 = 0 ∧ (w.lam * e.c w) % 2 = 0 ∧
    (e.K - e.s / 2) % 2 = 0 ∧ (w.k : ℤ) < 2 * e.K + 4 ∧ (2, e.r) ∈ MaRows.maPairs

instance EvenCert.instDecidableOk (w : Row) (e : EvenCert) : Decidable (e.Ok w) := by
  unfold EvenCert.Ok; infer_instance

/-- The search for the halved coset sums on `Grp (r :: ks)`. -/
def EvenCert.search (w : Row) (e : EvenCert) : Bool :=
  onGrp (e.r :: e.ks) fun n add => noVector n add (e.c w)
    ((w.k + w.lam * (2 * (e.c w : ℤ) - 1)) / 4) (w.lam * e.c w / 2) e.K (e.s / 2)

/-- `onGrp` from `f` at one positivity proof (to split a search into separate checks). -/
theorem onGrp_of {ds : List ℕ} {f : ℕ → (ℕ → ℕ → ℕ) → Bool} (h : ∀ d ∈ ds, 0 < d)
    (hf : f (@Indexed.size (Grp ds) _ (Grp.indexed ds h))
      (@Indexed.addIdx (Grp ds) _ (Grp.indexed ds h)) = true) : onGrp ds f = true := by
  unfold onGrp
  split_ifs
  exact hf

/-- A row C28 kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem EvenCert.not_hasSDS {w : Row} {e : EvenCert} (h : e.Ok w) (hnv : e.search w = true)
    (inst : Fintype (Grp w.ms)) : ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨hr, hi, -, hne, hks, hmap, hsurj, hprod, hn, hs, hs2, hQ, ht, hK1, hK2, hpair⟩ := h
  unfold EvenCert.search at hnv
  obtain ⟨hpos, hnv⟩ := onGrp_spec hnv
  unfold EvenCert.c at hQ ht hnv
  generalize hL : e.ks = L at hne hks hmap hsurj hprod hpos hnv hQ ht
  obtain ⟨k₀, ks, rfl⟩ := List.exists_cons_of_ne_nil hne
  have : NeZero (e.r * 2) := ⟨(Nat.mul_pos hr two_pos).ne'⟩
  have : NeZero e.r := ⟨hr.ne'⟩
  let _ : Fintype (Grp (k₀ :: ks)) :=
    Grp.fintype _ fun d hd => Nat.pos_of_dvd_of_pos (hks d hd) (by positivity)
  let _ : Indexed (ZMod e.r × Grp (k₀ :: ks)) := Grp.indexed (e.r :: k₀ :: ks) hpos
  let φ : Grp w.ms →+ ZMod (e.r * 2) × Grp (k₀ :: ks) :=
    linMap w.ms (e.r * 2 :: k₀ :: ks) e.A hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp w.ms) = w.ms.prod / (e.r * 2 * (k₀ :: ks).prod) *
      Fintype.card (ZMod (e.r * 2) × Grp (k₀ :: ks)) := by
    rw [Fintype.card_prod, ZMod.card, Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  have hconj (x : Grp (k₀ :: ks)) : 2 ^ e.i • x = -x := by
    have := Grp.nsmul_eq_zero (N := 2 ^ e.i + 1) (k₀ :: ks) hks x
    rw [add_smul, one_smul] at this
    exact eq_neg_of_add_eq_zero_left this
  refine not_hasSDS_of_evenContraction hφ hcard hr hi hconj hn
    (MaRows.cycloFacts_of_mem_maPairs hpair) (s := e.s) (s₂ := e.s / 2) (K' := e.K)
    (by rw [hs, Grp.card_eq]) (by omega) (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hQ))
    (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero ht)) hK1 hK2 hnv

end SignedDifferenceSets

#print axioms SignedDifferenceSets.onGrp_of
#print axioms SignedDifferenceSets.EvenCert.not_hasSDS
#print axioms SignedDifferenceSets.not_hasSDS_of_evenContraction
