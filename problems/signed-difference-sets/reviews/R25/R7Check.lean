import SignedDifferenceSets.SylowCheck
import SignedDifferenceSets.Answer.N79
import SignedDifferenceSets.Answer.N80



/-!
# C22 at `p = 2`: the equality part

With `n = m²` and `w = v₂(m) < t`, the characters of the Sylow 2-quotient split into the trivial
one (the sign sum `s'`), the real ones (values `± m`, an odd number of them:
`odd_card_two_torsion`) and pairs `χ, χ̄` with `χ(Y) + χ̄(Y) ∈ π^(wφ+1) A` (`add_conj_mem`,
`sum_mem_of_pairs`). So `2^t Y(0) ≡ s' + m T mod 2^(w+1)` with `T` odd, and `2^(w+1) ∤ s`
(`not_hasSDS_of_sylow_two`). `SyTwoCert` checks it on the table's rows.
-/


open Polynomial

namespace SignedDifferenceSets.SylowTrace

open Ma

variable {r : ℕ} [NeZero (r * 2)]

omit [NeZero (r * 2)] in
/-- For `p = 2`, `ρ^r = −1`. -/
theorem root_pow_r : AdjoinRoot.root (psi (Rg Unit) 2 r) ^ r = -1 := by
  have := sum_root_pow (K := Unit) (p := 2) (r := r)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at this
  linear_combination this

/-- In `ZMod (r 2)`, an element killed by `2` is `0` or `r`. -/
theorem eq_zero_or_eq_r_of_two_mul {x : ZMod (r * 2)} (hx : 2 * x = 0) :
    x = 0 ∨ x = (r : ZMod (r * 2)) := by
  have hr := r_pos 2 r
  have hv := ZMod.val_lt x
  have h2 : (2 * x.val) % (r * 2) = 0 := by
    have := congrArg ZMod.val hx
    rw [ZMod.val_mul, ZMod.val_zero] at this
    have h2v : (2 : ZMod (r * 2)).val = 2 % (r * 2) := by
      rw [show (2 : ZMod (r * 2)) = ((2 : ℕ) : ZMod (r * 2)) by norm_cast, ZMod.val_natCast]
    rw [h2v, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod] at this
    exact this
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h2
  have : x.val = 0 ∨ x.val = r := by
    rcases c with _ | _ | c
    · left; omega
    · right; omega
    · exfalso; nlinarith
  rcases this with h | h
  · left; rwa [ZMod.val_eq_zero] at h
  · right; rw [← ZMod.natCast_zmod_val x, h]

/-- A real character (`2u = 0`) takes the values `±1`: `ρ^⟨u, h⟩ = ±1`. -/
theorem root_pow_pair_of_two (ds : List ℕ) (hd : Divides (r * 2) ds) {u : Grp ds}
    (hu : 2 • u = 0) (h : Grp ds) :
    AdjoinRoot.root (psi (Rg Unit) 2 r) ^ (pair (r * 2) ds u h).val = 1 ∨
      AdjoinRoot.root (psi (Rg Unit) 2 r) ^ (pair (r * 2) ds u h).val = -1 := by
  have h2 : 2 * pair (r * 2) ds u h = 0 := by
    have := pair_add_left ds hd u u h
    rw [← two_nsmul, hu, pair_zero_left ds hd] at this
    linear_combination -this
  rcases eq_zero_or_eq_r_of_two_mul h2 with h0 | hr
  · left; rw [h0, ZMod.val_zero, pow_zero]
  · right
    rw [hr, ZMod.val_cast_of_lt (lt_mul_of_one_lt_right (r_pos 2 r) one_lt_two), root_pow_r]

/-- `σ` fixes the image of `ℤ`, and `red` of `σ`'s fixed-point defect vanishes for `p = 2`:
`x + σ(x)` lies in `π^(a+1) A` when `x` lies in `π^a A`. -/
theorem add_conj_mem (a : ℕ) {x y : A Unit 2 r}
    (hx : x = (AdjoinRoot.root _ - 1) ^ a * y) :
    ∃ z : A Unit 2 r, x + conj (K := Unit) 2 r x = (AdjoinRoot.root _ - 1) ^ (a + 1) * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set u := AdjoinRoot.root (psi (Rg Unit) 2 r) ^ (r * 2 - 1)
  have hc : conj (K := Unit) 2 r (AdjoinRoot.root _ - 1) = -u * (AdjoinRoot.root _ - 1) :=
    conj_root_sub_one
  have hsum : x + conj (K := Unit) 2 r x =
      (AdjoinRoot.root _ - 1) ^ a * (y + (-u) ^ a * conj (K := Unit) 2 r y) := by
    rw [hx, map_mul, map_pow, hc, mul_pow]
    ring
  have hred : red (K := Unit) 2 r (y + (-u) ^ a * conj (K := Unit) 2 r y) = 0 := by
    have hu : red (K := Unit) 2 r u = 1 := by rw [map_pow, red_root, one_pow]
    have hneg : AddMonoidAlgebra.mapDomainRingHom (ZMod 2) (negAddMonoidHom : Unit →+ Unit) =
        RingHom.id _ := by
      ext <;> simp
    rw [map_add, map_mul, map_pow, map_neg, hu, red_conj, hneg, RingHom.id_apply]
    have h2 : (2 : AddMonoidAlgebra (ZMod 2) Unit) = 0 := CharP.cast_eq_zero _ 2
    rcases neg_one_pow_eq_or (AddMonoidAlgebra (ZMod 2) Unit) a with h | h
    · rw [h, one_mul, ← two_mul, h2, zero_mul]
    · rw [h, neg_one_mul, add_neg_cancel]
  obtain ⟨z, hz⟩ := exists_of_red_eq_zero hred
  exact ⟨z, by rw [hsum, hz, pow_succ]; ring⟩

/-! ### Pairs and the count of real characters -/

/-- A sum over a set closed under a fixed-point-free involution lies in an ideal when each pair
`f i + f (e i)` does. -/
theorem sum_mem_of_pairs {ι R : Type*} [CommRing R] (I : Ideal R) (e : ι → ι)
    (he : ∀ i, e (e i) = i) (f : ι → R) :
    ∀ S : Finset ι, (∀ i ∈ S, e i ∈ S ∧ e i ≠ i) → (∀ i ∈ S, f i + f (e i) ∈ I) →
      ∑ i ∈ S, f i ∈ I := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS hf
    rcases S.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp
    · obtain ⟨hei, hne⟩ := hS i hi
      have hei' : e i ∈ S.erase i := Finset.mem_erase.2 ⟨hne, hei⟩
      have hsub : (S.erase i).erase (e i) ⊂ S :=
        (Finset.erase_subset _ _).trans_ssubset (Finset.erase_ssubset hi)
      have hsplit : ∑ j ∈ S, f j = f i + f (e i) + ∑ j ∈ (S.erase i).erase (e i), f j := by
        rw [← Finset.add_sum_erase S f hi, ← Finset.add_sum_erase (S.erase i) f hei', add_assoc]
      rw [hsplit]
      refine I.add_mem (hf i hi) (ih _ hsub (fun j hj => ?_) (fun j hj => hf j ?_))
      · simp only [Finset.mem_erase] at hj ⊢
        obtain ⟨hj1, hj2, hj3⟩ := hj
        obtain ⟨hej, hnej⟩ := hS j hj3
        refine ⟨⟨fun h => hj2 (by have := congrArg e h; rwa [he, he] at this),
          fun h => hj1 (by rw [← h, he]), hej⟩, hnej⟩
      · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hj)

/-- A group of order `2^t`, `t ≥ 1`, has an odd number of nonzero elements killed by `2`. -/
theorem odd_card_two_torsion {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H] {t : ℕ}
    (ht : Fintype.card H = 2 ^ t) (ht1 : 1 ≤ t) :
    Odd ((Finset.univ.erase (0 : H)).filter fun u => 2 • u = 0).card := by
  set F := (nsmulAddMonoidHom 2 : H →+ H).ker
  have hcard : Nat.card F = (Finset.univ.filter fun u : H => 2 • u = 0).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun u => by
      simp [F, AddMonoidHom.mem_ker])
  have hdvd : Nat.card F ∣ 2 ^ t := by
    rw [← ht, ← Nat.card_eq_fintype_card]
    exact AddSubgroup.card_addSubgroup_dvd_card F
  obtain ⟨R, -, hR⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card 2 (by rw [ht]; exact dvd_pow_self 2 (by omega))
  have hx2 : 2 • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, addOrderOf_zero] at hx
    omega
  have hR1 : 1 ≤ R := by
    by_contra h
    have hR0 : R = 0 := by omega
    have hle : 2 ≤ (Finset.univ.filter fun u : H => 2 • u = 0).card := by
      have : ({0, x} : Finset H) ⊆ Finset.univ.filter fun u : H => 2 • u = 0 := by
        intro y hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> simp [hx2]
      have h2 := Finset.card_le_card this
      rwa [Finset.card_pair hx0.symm] at h2
    rw [← hcard, hR, hR0, pow_zero] at hle
    omega
  have hfilter : ((Finset.univ.erase (0 : H)).filter fun u => 2 • u = 0) =
      (Finset.univ.filter fun u : H => 2 • u = 0).erase 0 := by
    ext u
    simp [and_comm]
  rw [hfilter, Finset.card_erase_of_mem (by simp), ← hcard, hR]
  rw [Nat.odd_sub (Nat.one_le_two_pow)]
  simp [Nat.even_pow, show R ≠ 0 by omega]


theorem chr_neg_left (ds : List ℕ) (hd : Divides (r * 2) ds) [Fintype (Grp ds)] (u : Grp ds)
    (Y : Grp ds → ℤ) :
    chr ds hd (-u) (ofFun Y) = conj (K := Unit) 2 r (chr ds hd u (ofFun Y)) := by
  rw [chr_ofFun, chr_ofFun, map_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_zsmul, map_pow, conj_root, root_pow_neg, pair_comm, pair_neg_right ds hd, pair_comm]

end SignedDifferenceSets.SylowTrace

namespace SignedDifferenceSets

open SylowTrace Ma

/-- C22 at `p = 2`, the equality part: with `n = m²`, `w = v₂(m) < t`, `2^(w+1) ∤ s`. -/
theorem not_hasSDS_of_sylow_two {G : Type*} [AddCommGroup G] [Fintype G] (ds : List ℕ)
    [Fintype (Grp ds)] {r : ℕ} [NeZero (r * 2)] (hd : PPowers 2 (r * 2) ds)
    (φ : G →+ Grp ds) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card (Grp ds)) {k : ℕ} {lam : ℤ} {m : ℤ} {w t : ℕ}
    (hm : (k : ℤ) - lam = m ^ 2) (hw : (2 : ℤ) ^ w ∣ m) (hw1 : ¬ (2 : ℤ) ^ (w + 1) ∣ m)
    (hwt : w < t) (ht : Fintype.card (Grp ds) = 2 ^ t) {s : ℤ}
    (hs : s ^ 2 = k + lam * ((c : ℤ) * Fintype.card (Grp ds) - 1))
    (hkill : (2 : ℤ) ^ (w + 1) ∣ s)
    (hcert : ∀ (S : Type) [CommRing S] (x : S), ∑ l ∈ Finset.range 2, (x ^ r) ^ l = 0 →
      ∃ y z : S, (2 : S) = (x - 1) ^ ((2 - 1) * r) * y ∧ (x - 1) ^ ((2 - 1) * r) = 2 * z) :
    ¬ HasSDS G k lam := by
  intro ⟨D, hD⟩
  have hp : Nat.Prime 2 := Nat.prime_two
  set Y := contract φ D with hYdef
  have hY : ∀ g, ∑ h, Y h * Y (h + g) = (if g = 0 then (k : ℤ) - lam else 0) + lam * c := by
    intro g
    by_cases hg : g = 0
    · subst hg
      simp only [add_zero, ite_true]
      rw [hD.contract_sq φ, card_fibre_eq hφ hcard, Nat.cast_sub (one_le_of_card hcard),
        Nat.cast_one]
      ring
    · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcard, ite_eq_right hg, zero_add]
  obtain ⟨yc, zc, hpc, hzc⟩ := hcert (A Unit 2 r) (AdjoinRoot.root _) sum_root_pow
  have hpc' : ((2 : ℕ) : A Unit 2 r) = (AdjoinRoot.root _ - 1) ^ ((2 - 1) * r) * yc := by
    rw [Nat.cast_ofNat]; exact hpc
  have hzc' : (AdjoinRoot.root _ - 1) ^ ((2 - 1) * r) = ((2 : ℕ) : A Unit 2 r) * zc := by
    rw [Nat.cast_ofNat]; exact hzc
  set φ' := (2 - 1) * r
  obtain ⟨m', hm'⟩ := hw
  have hc1 : ∀ x : Unit, 2 ^ 1 • x = -x := fun x => Subsingleton.elim _ _
  -- every nontrivial character value lies in `π^(w φ') A`
  have hX : ∀ u : Grp ds, u ≠ 0 → ∃ x : A Unit 2 r,
      chr ds hd.divides u (ofFun Y) = (AdjoinRoot.root _ - 1) ^ (w * φ') * x := by
    intro u hu
    have hN : chr ds hd.divides u (ofFun Y) * conj (K := Unit) 2 r
        (chr ds hd.divides u (ofFun Y)) =
        (AdjoinRoot.root (psi (Rg Unit) 2 r) - 1) ^ (2 * w * φ') * (yc ^ (2 * w) * m' ^ 2) := by
      rw [chr_mul_conj hp ds hd hzc' hu hY, hm, hm', mul_pow, ← pow_mul, Int.cast_mul,
        Int.cast_pow, Int.cast_pow, Int.cast_ofNat, ← Nat.cast_ofNat (R := A Unit 2 r), hpc',
        mul_pow, ← pow_mul]
      ring
    obtain ⟨x, hx⟩ := exists_pow_mul (two_ne_zero) one_pos hc1 hN (w * φ') (by ring_nf; omega)
    exact ⟨x, hx⟩
  -- real characters: integers `± m`
  have hreal : ∀ u : Grp ds, 2 • u = 0 → u ≠ 0 → ∃ z : ℤ,
      chr ds hd.divides u (ofFun Y) = (z : A Unit 2 r) ∧ (z = m ∨ z = -m) := by
    intro u hu2 hu
    classical
    have hpm := fun h => root_pow_pair_of_two ds hd.divides hu2 h
    set ε : Grp ds → ℤ := fun h =>
      if AdjoinRoot.root (psi (Rg Unit) 2 r) ^ (pair (r * 2) ds u h).val = 1 then 1 else -1
    have hε : ∀ h, AdjoinRoot.root (psi (Rg Unit) 2 r) ^ (pair (r * 2) ds u h).val =
        ((ε h : ℤ) : A Unit 2 r) := by
      intro h
      simp only [ε]
      split_ifs with h1
      · rw [h1, Int.cast_one]
      · rcases hpm h with h2 | h2
        · exact absurd h2 h1
        · rw [h2, Int.cast_neg, Int.cast_one]
    have hz : chr ds hd.divides u (ofFun Y) = ((∑ h, Y h * ε h : ℤ) : A Unit 2 r) := by
      rw [chr_ofFun, Int.cast_sum]
      exact Finset.sum_congr rfl fun h _ => by rw [hε, zsmul_eq_mul, Int.cast_mul]
    refine ⟨∑ h, Y h * ε h, hz, ?_⟩
    have hn := chr_mul_conj hp ds hd hzc' hu hY
    rw [hz, map_intCast, ← Int.cast_mul] at hn
    have hsq : (∑ h, Y h * ε h) * (∑ h, Y h * ε h) = m ^ 2 := by
      rw [← hm]
      have := intCast_eq_zero (K := Unit) (p := 2) (r := r) one_lt_two (r_pos 2 r)
        (z := (∑ h, Y h * ε h) * (∑ h, Y h * ε h) - ((k : ℤ) - lam)) (by
          rw [Int.cast_sub, hn, sub_self])
      linarith
    have hsq' : (∑ h, Y h * ε h) ^ 2 = m ^ 2 := by rw [sq]; exact hsq
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq' with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hm0 : m ≠ 0 := fun h => hw1 (by rw [h]; exact dvd_zero _)
  classical
  choose zr hzr using hreal
  have hsplit := sum_chr hp ds hd hzc' Y
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Grp ds)), chr_zero,
    ← Finset.sum_filter_add_sum_filter_not (Finset.univ.erase (0 : Grp ds))
      (fun u => 2 • u = 0)] at hsplit
  set π := AdjoinRoot.root (psi (Rg Unit) 2 r) - 1
  set I : Ideal (A Unit 2 r) := Ideal.span {π ^ (w * φ' + 1)}
  set R2 := (Finset.univ.erase (0 : Grp ds)).filter fun u => 2 • u = 0
  set NR := (Finset.univ.erase (0 : Grp ds)).filter fun u => ¬ 2 • u = 0
  have hNR : ∑ u ∈ NR, chr ds hd.divides u (ofFun Y) ∈ I := by
    refine sum_mem_of_pairs I Neg.neg neg_neg _ NR (fun u hu => ?_) (fun u hu => ?_)
    · simp only [NR, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hu ⊢
      refine ⟨⟨neg_ne_zero.2 hu.1, fun h => hu.2 (by rw [smul_neg, neg_eq_zero] at h; exact h)⟩,
        fun h => hu.2 ?_⟩
      have h2 : -u + u = 0 := neg_add_cancel u
      rw [h] at h2
      rw [two_nsmul]
      exact h2
    · have hu0 : u ≠ 0 := (Finset.mem_erase.1 (Finset.mem_of_mem_filter u hu)).1
      obtain ⟨x, hx⟩ := hX u hu0
      obtain ⟨z, hz⟩ := add_conj_mem (w * φ') hx
      rw [chr_neg_left, hz]
      exact Ideal.mem_span_singleton'.2 ⟨z, mul_comm _ _⟩
  obtain ⟨wnr, hwnr⟩ := Ideal.mem_span_singleton'.1 hNR
  have hR2 : ∑ u ∈ R2, chr ds hd.divides u (ofFun Y) =
      ((∑ u ∈ R2.attach, zr u.1 (Finset.mem_filter.1 u.2).2
        (Finset.mem_erase.1 (Finset.mem_of_mem_filter _ u.2)).1 : ℤ) : A Unit 2 r) := by
    rw [Int.cast_sum, ← Finset.sum_attach R2]
    exact Finset.sum_congr rfl fun u _ => (hzr _ _ _).1
  set ZR := ∑ u ∈ R2.attach, zr u.1 (Finset.mem_filter.1 u.2).2
    (Finset.mem_erase.1 (Finset.mem_of_mem_filter _ u.2)).1
  have hdiff : ((Fintype.card (Grp ds) * Y 0 - ∑ h, Y h - ZR : ℤ) : A Unit 2 r) =
      π ^ (w * φ' + 1) * wnr := by
    rw [hR2] at hsplit
    push_cast at hsplit ⊢
    rw [mul_comm (π ^ (w * φ' + 1)) wnr, hwnr]
    linear_combination -hsplit
  have hdvd := dvd_of_eq_pow_mul hp hpc' hzc' w _ _ hdiff
  -- `ZR = m T` with `T` odd
  set T := ∑ u ∈ R2.attach, (if zr u.1 (Finset.mem_filter.1 u.2).2
    (Finset.mem_erase.1 (Finset.mem_of_mem_filter _ u.2)).1 = m then (1 : ℤ) else -1)
  have hZR : ZR = m * T := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rcases (hzr _ _ _).2 with h | h
    · rw [ite_eq_left h, h, mul_one]
    · by_cases h' : -m = m
      · exfalso; exact hm0 (by linarith)
      · rw [h, ite_eq_right h', mul_neg_one]
  have hT : Odd T := by
    have hcnt := odd_card_two_torsion ht (by omega)
    have heven : Even (T - R2.attach.card) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ← Finset.sum_sub_distrib]
      refine Finset.even_sum _ fun u _ => ?_
      split_ifs
      · simp
      · exact ⟨-1, by ring⟩
    rw [Finset.card_attach] at heven
    have : Odd (R2.card : ℤ) := by exact_mod_cast hcnt
    have := heven.add_odd this
    simpa using this
  have hs' : (2 : ℤ) ^ (w + 1) ∣ ∑ h, Y h := by
    have hsq := hD.sum_contract_sq φ hφ hcard
    rw [← hs] at hsq
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
    · rw [h]; exact hkill
    · rw [h]; exact (dvd_neg).2 hkill
  have hcardY : (2 : ℤ) ^ (w + 1) ∣ (Fintype.card (Grp ds) : ℤ) * Y 0 := by
    rw [ht]
    push_cast
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _
  have hmT : (2 : ℤ) ^ (w + 1) ∣ m * T := by
    rw [← hZR]
    have h1 := dvd_sub (dvd_sub hcardY hs') hdvd
    simpa using h1
  have hcop : IsCoprime ((2 : ℤ) ^ (w + 1)) T := by
    apply IsCoprime.pow_left
    obtain ⟨a, ha⟩ := hT
    exact ⟨-a, 1, by rw [ha]; ring⟩
  exact hw1 (hcop.dvd_of_dvd_mul_right hmT)

/-- A C22 (`p = 2`) certificate: `r = 2^(J−1)`, `m = √(k − λ)`, `w = v₂(m)`, `t`, `s` and the
quotient. -/
structure SyTwoCert where
  r : ℕ
  m : ℤ
  w : ℕ
  t : ℕ
  s : ℤ
  ds : List ℕ
  deriving DecidableEq

/-- The `p = 2` equality part kills the row. -/
def SyTwoCert.Kills (r : Row) (c : SyTwoCert) : Prop :=
  0 < c.r ∧ (∀ m ∈ r.ms, 0 < m) ∧ Dvds c.ds r.ms ∧ PPowersB 2 (c.r * 2) c.ds ∧
    (r.k : ℤ) - r.lam = c.m ^ 2 ∧ (2 : ℤ) ^ c.w ∣ c.m ∧ ¬ (2 : ℤ) ^ (c.w + 1) ∣ c.m ∧
    c.w < c.t ∧ c.ds.prod = 2 ^ c.t ∧ c.s ^ 2 = r.k + r.lam * ((r.ms.prod : ℤ) - 1) ∧
    (2 : ℤ) ^ (c.w + 1) ∣ c.s ∧ (2, c.r) ∈ MaRows.maPairs

instance SyTwoCert.instDecidableKills (r : Row) (c : SyTwoCert) : Decidable (c.Kills r) := by
  unfold SyTwoCert.Kills; infer_instance

/-- A row the `p = 2` equality kills has no SDS, whatever `Fintype` instance its group carries. -/
theorem SyTwoCert.not_hasSDS {r : Row} {c : SyTwoCert} (h : c.Kills r)
    (inst : Fintype (Grp r.ms)) : ¬ @HasSDS (Grp r.ms) _ inst r.k r.lam := by
  obtain ⟨hr, hms, hdv, hpp, hm, hw, hw1, hwt, ht, hs, hkill, hpair⟩ := h
  have : NeZero (c.r * 2) := ⟨Nat.mul_ne_zero hr.ne' two_ne_zero⟩
  let _ : Fintype (Grp c.ds) := Grp.fintype c.ds (Dvds.pos _ _ hdv hms)
  have hprod := Dvds.prod_dvd _ _ hdv
  have hcard : Fintype.card (Grp r.ms) = (r.ms.prod / c.ds.prod) * Fintype.card (Grp c.ds) := by
    rw [Grp.card_eq, Grp.card_eq, Nat.div_mul_cancel hprod]
  refine not_hasSDS_of_sylow_two c.ds hpp.pPowers (quot r.ms c.ds hdv)
    (quot_surjective r.ms c.ds hdv) hcard hm hw hw1 hwt (by rw [Grp.card_eq, ht]) (s := c.s) ?_
    hkill (MaRows.cycloFacts_of_mem_maPairs hpair)
  rw [hs, Grp.card_eq, ← Nat.cast_mul, Nat.div_mul_cancel hprod]

end SignedDifferenceSets



/-!
# Rows killed by C22's equality part at `p = 2`

63 open rows, each with its Sylow 2-quotient, `m = √(k − λ)`, `w = v₂(m) < t` and
`2^(w+1) ∣ s`, checked by `SyTwoCert.Kills` in chunks of 50, one `decide +kernel` each;
generated by `solver/sylowtworows.py`.
-/


namespace SignedDifferenceSets

/-- Rows and certificates, chunk 1. -/
def sylowTwoRows1 : List (Row × SyTwoCert) := [
  (⟨2640, [2, 56], 84, 20⟩,
    ⟨4, 8, 3, 4, 48, [2, 8]⟩),
  (⟨2642, [112], 84, 20⟩,
    ⟨8, 8, 3, 4, 48, [16]⟩),
  (⟨2660, [2, 56], 100, 36⟩,
    ⟨4, 8, 3, 4, 64, [2, 8]⟩),
  (⟨2662, [112], 100, 36⟩,
    ⟨8, 8, 3, 4, 64, [16]⟩),
  (⟨2993, [120], 18, 2⟩,
    ⟨4, 4, 2, 3, 16, [8]⟩),
  (⟨3041, [120], 106, 90⟩,
    ⟨4, 4, 2, 3, 104, [8]⟩),
  (⟨8108, [184], 178, 34⟩,
    ⟨4, 12, 2, 3, 80, [8]⟩),
  (⟨12158, [2, 112], 74, 10⟩,
    ⟨8, 8, 3, 5, 48, [2, 16]⟩),
  (⟨12160, [224], 74, 10⟩,
    ⟨16, 8, 3, 5, 48, [32]⟩),
  (⟨12165, [2, 112], 82, 18⟩,
    ⟨8, 8, 3, 5, 64, [2, 16]⟩),
  (⟨12167, [224], 82, 18⟩,
    ⟨16, 8, 3, 5, 64, [32]⟩),
  (⟨12340, [2, 112], 178, 114⟩,
    ⟨8, 8, 3, 5, 160, [2, 16]⟩),
  (⟨12342, [224], 178, 114⟩,
    ⟨16, 8, 3, 5, 160, [32]⟩),
  (⟨12396, [2, 112], 202, 138⟩,
    ⟨8, 8, 3, 5, 176, [2, 16]⟩),
  (⟨12398, [224], 202, 138⟩,
    ⟨16, 8, 3, 5, 176, [32]⟩),
  (⟨14049, [2, 120], 68, 4⟩,
    ⟨4, 8, 3, 4, 32, [2, 8]⟩),
  (⟨14079, [2, 120], 116, 52⟩,
    ⟨4, 8, 3, 4, 112, [2, 8]⟩),
  (⟨14089, [2, 120], 132, 68⟩,
    ⟨4, 8, 3, 4, 128, [2, 8]⟩),
  (⟨20874, [280], 162, 18⟩,
    ⟨4, 12, 2, 3, 72, [8]⟩),
  (⟨20916, [280], 202, 58⟩,
    ⟨4, 12, 2, 3, 128, [8]⟩),
  (⟨20943, [280], 226, 82⟩,
    ⟨4, 12, 2, 3, 152, [8]⟩),
  (⟨25985, [312], 210, 66⟩,
    ⟨4, 12, 2, 3, 144, [8]⟩),
  (⟨26003, [312], 234, 90⟩,
    ⟨4, 12, 2, 3, 168, [8]⟩),
  (⟨27575, [8, 40], 268, 12⟩,
    ⟨4, 16, 4, 6, 64, [8, 8]⟩),
  (⟨27586, [8, 40], 284, 28⟩,
    ⟨4, 16, 4, 6, 96, [8, 8]⟩),
  (⟨30531, [2, 168], 76, 12⟩,
    ⟨4, 8, 3, 4, 64, [2, 8]⟩),
  (⟨30533, [336], 76, 12⟩,
    ⟨8, 8, 3, 4, 64, [16]⟩),
  (⟨30761, [2, 168], 284, 220⟩,
    ⟨4, 8, 3, 4, 272, [2, 8]⟩),
  (⟨30763, [336], 284, 220⟩,
    ⟨8, 8, 3, 4, 272, [16]⟩),
  (⟨35265, [3, 120], 150, 6⟩,
    ⟨4, 12, 2, 3, 48, [1, 8]⟩),
  (⟨35267, [360], 150, 6⟩,
    ⟨4, 12, 2, 3, 48, [8]⟩),
  (⟨35277, [3, 120], 158, 14⟩,
    ⟨4, 12, 2, 3, 72, [1, 8]⟩),
  (⟨35279, [360], 158, 14⟩,
    ⟨4, 12, 2, 3, 72, [8]⟩),
  (⟨35361, [3, 120], 222, 78⟩,
    ⟨4, 12, 2, 3, 168, [1, 8]⟩),
  (⟨35363, [360], 222, 78⟩,
    ⟨4, 12, 2, 3, 168, [8]⟩),
  (⟨35391, [3, 120], 246, 102⟩,
    ⟨4, 12, 2, 3, 192, [1, 8]⟩),
  (⟨35393, [360], 246, 102⟩,
    ⟨4, 12, 2, 3, 192, [8]⟩),
  (⟨38893, [376], 226, 82⟩,
    ⟨4, 12, 2, 3, 176, [8]⟩),
  (⟨38920, [376], 250, 106⟩,
    ⟨4, 12, 2, 3, 200, [8]⟩),
  (⟨40678, [8, 48], 258, 2⟩,
    ⟨8, 16, 4, 7, 32, [8, 16]⟩),
  (⟨40753, [8, 48], 266, 10⟩,
    ⟨8, 16, 4, 7, 64, [8, 16]⟩),
  (⟨40873, [8, 48], 298, 42⟩,
    ⟨8, 16, 4, 7, 128, [8, 16]⟩),
  (⟨41023, [8, 48], 322, 66⟩,
    ⟨8, 16, 4, 7, 160, [8, 16]⟩),
  (⟨46944, [408], 234, 90⟩,
    ⟨4, 12, 2, 3, 192, [8]⟩),
  (⟨46953, [408], 258, 114⟩,
    ⟨4, 12, 2, 3, 216, [8]⟩),
  (⟨54178, [440], 146, 2⟩,
    ⟨4, 12, 2, 3, 32, [8]⟩),
  (⟨54217, [440], 242, 98⟩,
    ⟨4, 12, 2, 3, 208, [8]⟩),
  (⟨54244, [440], 266, 122⟩,
    ⟨4, 12, 2, 3, 232, [8]⟩),
  (⟨56542, [2, 2, 112], 276, 20⟩,
    ⟨8, 16, 4, 6, 96, [2, 2, 16]⟩),
  (⟨56544, [2, 224], 276, 20⟩,
    ⟨16, 16, 4, 6, 96, [2, 32]⟩)]

set_option maxRecDepth 100000 in
theorem sylowTwoRows1_kill : ∀ x ∈ sylowTwoRows1, x.2.Kills x.1 := by decide +kernel

/-- No row of chunk 1 has an SDS. -/
theorem sylowTwoRows1_not_hasSDS {x : Row × SyTwoCert} (hx : x ∈ sylowTwoRows1)
    (inst : Fintype (Grp x.1.ms)) : ¬ @HasSDS (Grp x.1.ms) _ inst x.1.k x.1.lam :=
  SyTwoCert.not_hasSDS (sylowTwoRows1_kill x hx) inst

/-- Rows and certificates, chunk 2. -/
def sylowTwoRows2 : List (Row × SyTwoCert) := [
  (⟨56546, [4, 112], 276, 20⟩,
    ⟨8, 16, 4, 6, 96, [4, 16]⟩),
  (⟨56547, [8, 56], 276, 20⟩,
    ⟨4, 16, 4, 6, 96, [8, 8]⟩),
  (⟨56586, [2, 2, 112], 292, 36⟩,
    ⟨8, 16, 4, 6, 128, [2, 2, 16]⟩),
  (⟨56588, [2, 224], 292, 36⟩,
    ⟨16, 16, 4, 6, 128, [2, 32]⟩),
  (⟨56590, [4, 112], 292, 36⟩,
    ⟨8, 16, 4, 6, 128, [4, 16]⟩),
  (⟨56591, [8, 56], 292, 36⟩,
    ⟨4, 16, 4, 6, 128, [8, 8]⟩),
  (⟨64584, [2, 240], 66, 2⟩,
    ⟨8, 8, 3, 5, 32, [2, 16]⟩),
  (⟨64750, [2, 2, 120], 264, 8⟩,
    ⟨4, 16, 4, 5, 64, [2, 2, 8]⟩),
  (⟨64753, [4, 120], 264, 8⟩,
    ⟨4, 16, 4, 5, 64, [4, 8]⟩),
  (⟨64946, [2, 2, 120], 360, 104⟩,
    ⟨4, 16, 4, 5, 224, [2, 2, 8]⟩),
  (⟨64949, [4, 120], 360, 104⟩,
    ⟨4, 16, 4, 5, 224, [4, 8]⟩),
  (⟨65023, [2, 2, 120], 392, 136⟩,
    ⟨4, 16, 4, 5, 256, [2, 2, 8]⟩),
  (⟨65026, [4, 120], 392, 136⟩,
    ⟨4, 16, 4, 5, 256, [4, 8]⟩)]

set_option maxRecDepth 100000 in
theorem sylowTwoRows2_kill : ∀ x ∈ sylowTwoRows2, x.2.Kills x.1 := by decide +kernel

/-- No row of chunk 2 has an SDS. -/
theorem sylowTwoRows2_not_hasSDS {x : Row × SyTwoCert} (hx : x ∈ sylowTwoRows2)
    (inst : Fintype (Grp x.1.ms)) : ¬ @HasSDS (Grp x.1.ms) _ inst x.1.k x.1.lam :=
  SyTwoCert.not_hasSDS (sylowTwoRows2_kill x hx) inst

end SignedDifferenceSets



/-!
# N79: no (27, 22, 9) SDS in C₃ × C₃ × C₃

Open in Gordon's table (`SDS(27,22,9,[3,3,3])`, 2026-11-05).
Contract along C₃ × C₃ × C₃ → C₃ × C₃ (C3): fibres of 3 elements, so the coset
sums lie in [−3, 3], have square sum 22 + 9 · 2 = 40, sum ±16 and
autocorrelation 9 · 3 = 27 at every shift ≠ 0; `noVector` (`decide +kernel`)
finds no such vector. Quotient from E5; this file is generated by `solver/answer.py`.
-/


namespace SignedDifferenceSets.R7.N79

/-- The projection C₃ × C₃ × C₃ → C₃ × C₃, factor by factor. -/
def proj : Proj (ZMod 3 × ZMod 3 × ZMod 3) (ZMod 3 × ZMod 3 × ZMod 1) :=
  .prod (.cast 3 (by norm_num))
    (.prod (.cast 3 (by norm_num))
    (.cast 1 (by norm_num)))

set_option maxRecDepth 100000 in
-- `decide +kernel` runs the vector search.
/-- N79: C₃ × C₃ × C₃ has no signed difference set with parameters (27, 22, 9). -/
theorem not_hasSDS : ¬ HasSDS (ZMod 3 × ZMod 3 × ZMod 3) 22 9 :=
  not_hasSDS_of_noVector proj 3 16 (by simp [Fintype.card_prod, ZMod.card])
    (by norm_num [Fintype.card_prod, ZMod.card]) (by decide +kernel)

end SignedDifferenceSets.R7.N79



/-!
# N80: no (27, 22, 9) SDS in C₃ × C₉

Open in Gordon's table (`SDS(27,22,9,[3,9])`, 2026-11-05).
Contract along C₃ × C₉ → C₃ × C₃ (C3): fibres of 3 elements, so the coset
sums lie in [−3, 3], have square sum 22 + 9 · 2 = 40, sum ±16 and
autocorrelation 9 · 3 = 27 at every shift ≠ 0; `noVector` (`decide +kernel`)
finds no such vector. Quotient from E5; this file is generated by `solver/answer.py`.
-/


namespace SignedDifferenceSets.R7.N80

/-- The projection C₃ × C₉ → C₃ × C₃, factor by factor. -/
def proj : Proj (ZMod 3 × ZMod 9) (ZMod 3 × ZMod 3) :=
  .prod (.cast 3 (by norm_num))
    (.cast 3 (by norm_num))

set_option maxRecDepth 100000 in
-- `decide +kernel` runs the vector search.
/-- N80: C₃ × C₉ has no signed difference set with parameters (27, 22, 9). -/
theorem not_hasSDS : ¬ HasSDS (ZMod 3 × ZMod 9) 22 9 :=
  not_hasSDS_of_noVector proj 3 16 (by simp [Fintype.card_prod, ZMod.card])
    (by norm_num [Fintype.card_prod, ZMod.card]) (by decide +kernel)

end SignedDifferenceSets.R7.N80


open SignedDifferenceSets
#print axioms SignedDifferenceSets.not_hasSDS_of_sylow_two
#print axioms SignedDifferenceSets.SyTwoCert.not_hasSDS
#print axioms SignedDifferenceSets.sylowTwoRows1_not_hasSDS
#print axioms SignedDifferenceSets.sylowTwoRows2_not_hasSDS
#print axioms SignedDifferenceSets.sylowTwoRows1_kill
#print axioms SignedDifferenceSets.sylowTwoRows2_kill
#print axioms SignedDifferenceSets.Answer.N79.not_hasSDS
#print axioms SignedDifferenceSets.Answer.N80.not_hasSDS
#print axioms SignedDifferenceSets.R7.N79.not_hasSDS
#print axioms SignedDifferenceSets.R7.N80.not_hasSDS
#check @SignedDifferenceSets.not_hasSDS_of_sylow_two
#check @SignedDifferenceSets.Answer.N79.not_hasSDS
#check @SignedDifferenceSets.Answer.N80.not_hasSDS

set_option maxRecDepth 100000 in
example : sylowTwoRows1.map (fun x => (x.1.id, x.1.ms, x.1.k, x.1.lam)) =
  [(2640, [2, 56], 84, (20 : ℤ)),
  (2642, [112], 84, (20 : ℤ)),
  (2660, [2, 56], 100, (36 : ℤ)),
  (2662, [112], 100, (36 : ℤ)),
  (2993, [120], 18, (2 : ℤ)),
  (3041, [120], 106, (90 : ℤ)),
  (8108, [184], 178, (34 : ℤ)),
  (12158, [2, 112], 74, (10 : ℤ)),
  (12160, [224], 74, (10 : ℤ)),
  (12165, [2, 112], 82, (18 : ℤ)),
  (12167, [224], 82, (18 : ℤ)),
  (12340, [2, 112], 178, (114 : ℤ)),
  (12342, [224], 178, (114 : ℤ)),
  (12396, [2, 112], 202, (138 : ℤ)),
  (12398, [224], 202, (138 : ℤ)),
  (14049, [2, 120], 68, (4 : ℤ)),
  (14079, [2, 120], 116, (52 : ℤ)),
  (14089, [2, 120], 132, (68 : ℤ)),
  (20874, [280], 162, (18 : ℤ)),
  (20916, [280], 202, (58 : ℤ)),
  (20943, [280], 226, (82 : ℤ)),
  (25985, [312], 210, (66 : ℤ)),
  (26003, [312], 234, (90 : ℤ)),
  (27575, [8, 40], 268, (12 : ℤ)),
  (27586, [8, 40], 284, (28 : ℤ)),
  (30531, [2, 168], 76, (12 : ℤ)),
  (30533, [336], 76, (12 : ℤ)),
  (30761, [2, 168], 284, (220 : ℤ)),
  (30763, [336], 284, (220 : ℤ)),
  (35265, [3, 120], 150, (6 : ℤ)),
  (35267, [360], 150, (6 : ℤ)),
  (35277, [3, 120], 158, (14 : ℤ)),
  (35279, [360], 158, (14 : ℤ)),
  (35361, [3, 120], 222, (78 : ℤ)),
  (35363, [360], 222, (78 : ℤ)),
  (35391, [3, 120], 246, (102 : ℤ)),
  (35393, [360], 246, (102 : ℤ)),
  (38893, [376], 226, (82 : ℤ)),
  (38920, [376], 250, (106 : ℤ)),
  (40678, [8, 48], 258, (2 : ℤ)),
  (40753, [8, 48], 266, (10 : ℤ)),
  (40873, [8, 48], 298, (42 : ℤ)),
  (41023, [8, 48], 322, (66 : ℤ)),
  (46944, [408], 234, (90 : ℤ)),
  (46953, [408], 258, (114 : ℤ)),
  (54178, [440], 146, (2 : ℤ)),
  (54217, [440], 242, (98 : ℤ)),
  (54244, [440], 266, (122 : ℤ)),
  (56542, [2, 2, 112], 276, (20 : ℤ)),
  (56544, [2, 224], 276, (20 : ℤ))] := by decide +kernel

set_option maxRecDepth 100000 in
example : sylowTwoRows2.map (fun x => (x.1.id, x.1.ms, x.1.k, x.1.lam)) =
  [(56546, [4, 112], 276, (20 : ℤ)),
  (56547, [8, 56], 276, (20 : ℤ)),
  (56586, [2, 2, 112], 292, (36 : ℤ)),
  (56588, [2, 224], 292, (36 : ℤ)),
  (56590, [4, 112], 292, (36 : ℤ)),
  (56591, [8, 56], 292, (36 : ℤ)),
  (64584, [2, 240], 66, (2 : ℤ)),
  (64750, [2, 2, 120], 264, (8 : ℤ)),
  (64753, [4, 120], 264, (8 : ℤ)),
  (64946, [2, 2, 120], 360, (104 : ℤ)),
  (64949, [4, 120], 360, (104 : ℤ)),
  (65023, [2, 2, 120], 392, (136 : ℤ)),
  (65026, [4, 120], 392, (136 : ℤ))] := by decide +kernel

-- plain types
example : ¬ HasSDS (ZMod 120) 18 2 :=
  sylowTwoRows1_not_hasSDS (x := (⟨2993, [120], 18, 2⟩, ⟨4, 4, 2, 3, 16, [8]⟩)) (by decide +kernel) inferInstance
example : ¬ HasSDS (ZMod 4 × ZMod 120) 392 136 :=
  sylowTwoRows2_not_hasSDS (x := (⟨65026, [4, 120], 392, 136⟩, ⟨4, 16, 4, 5, 256, [4, 8]⟩)) (by decide +kernel) inferInstance
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 112) 276 20 :=
  sylowTwoRows1_not_hasSDS (x := (⟨56542, [2, 2, 112], 276, 20⟩, ⟨8, 16, 4, 6, 96, [2, 2, 16]⟩)) (by decide +kernel) inferInstance
example : ¬ HasSDS (ZMod 3 × ZMod 120) 150 6 :=
  sylowTwoRows1_not_hasSDS (x := (⟨35265, [3, 120], 150, 6⟩, ⟨4, 12, 2, 3, 48, [1, 8]⟩)) (by decide +kernel) inferInstance
-- controls: each must be decided false
-- O13 (32,20,4) on C2 x C16, s = 12: 8 does not divide 12
example : ¬ (SyTwoCert.Kills ⟨0, [2, 16], 20, 4⟩ ⟨8, 4, 2, 5, 12, [2, 16]⟩) := by decide +kernel
-- N2993 with w one too small / too large
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨4, 4, 1, 3, 16, [8]⟩) := by decide +kernel
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨4, 4, 3, 3, 16, [8]⟩) := by decide +kernel
-- N2993 with k changed to 19, r = 3 (not in maPairs), non-2-power factor 24
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 19, 2⟩ ⟨4, 4, 2, 3, 16, [8]⟩) := by decide +kernel
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨3, 4, 2, 3, 16, [8]⟩) := by decide +kernel
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨12, 4, 2, 3, 16, [24]⟩) := by decide +kernel
-- w = t: N2993 cert with t claimed 2 but ds [8]
example : ¬ (SyTwoCert.Kills ⟨2993, [120], 18, 2⟩ ⟨4, 4, 2, 2, 16, [8]⟩) := by decide +kernel
