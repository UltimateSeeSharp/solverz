module

public import SignedDifferenceSets.MaLemma
public import SignedDifferenceSets.Moments
public import SignedDifferenceSets.Rows

/-!
# C22: the Sylow trace rule, divisibility form

On a quotient `Grp ds` whose factors are powers of `p` dividing `N = r p`, the characters
`h ↦ ρ^⟨u, h⟩` (`chr`, `pair`) map into `A = ℤ[X]/(Ψ)` (MaLemma's ring with `K` trivial). For
`u ≠ 0`, `χ_u(Y) σ(χ_u(Y)) = n` (`chr_mul_conj`), so `χ_u(Y) ∈ π^(q φ + 1) A` when
`2 (q φ + 1) ≤ e φ` (`exists_pow_mul`); the sum over all characters is `|H| Y(0)` (`sum_chr`),
so `|H| Y(0) − ∑ Y` is an integer in `π^(q φ + 1) A`, hence divisible by `p^(q+1)`
(`dvd_of_eq_pow_mul`). `not_hasSDS_of_sylow`: no SDS when `p^min(t, q+1) ∤ s`.
-/

@[expose] public section

open Polynomial

namespace SignedDifferenceSets.SylowTrace

open Ma

/-! ### The pairing `Grp ds × Grp ds → ZMod N` -/

/-- `x ↦ (N / d) x`, `ZMod d → ZMod N` (additive when `d ∣ N`). -/
def embed (N d : ℕ) (x : ZMod d) : ZMod N := ((x.val * (N / d) : ℕ) : ZMod N)

theorem embed_zero (N d : ℕ) : embed N d 0 = 0 := by simp [embed]

theorem embed_add {N d : ℕ} [NeZero d] (hd : d ∣ N) (x y : ZMod d) :
    embed N d (x + y) = embed N d x + embed N d y := by
  obtain ⟨c, rfl⟩ := hd
  have hc : d * c / d = c := Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero (NeZero.ne d))
  simp only [embed, hc, ZMod.val_add]
  have e := Nat.mod_add_div (x.val + y.val) d
  have : ((x.val + y.val) * c : ℕ) =
      ((x.val + y.val) % d * c + (x.val + y.val) / d * (d * c) : ℕ) := by
    conv_lhs => rw [← e]
    ring
  have key : (((x.val + y.val) % d * c : ℕ) : ZMod (d * c)) =
      (((x.val + y.val) * c : ℕ) : ZMod (d * c)) := by
    rw [this, Nat.cast_add, Nat.cast_mul ((x.val + y.val) / d), ZMod.natCast_self, mul_zero,
      add_zero]
  rw [key]
  push_cast
  ring

theorem embed_neg {N d : ℕ} [NeZero d] (hd : d ∣ N) (x : ZMod d) :
    embed N d (-x) = -embed N d x := by
  have := embed_add hd (-x) x
  rw [neg_add_cancel, embed_zero] at this
  linear_combination -this

/-- The pairing `∑ᵢ (N / dᵢ) uᵢ hᵢ`. -/
def pair (N : ℕ) : (ds : List ℕ) → Grp ds → Grp ds → ZMod N
  | [], _, _ => 0
  | [d], u, h => embed N d (u * h)
  | d :: d' :: ds, u, h => embed N d (u.1 * h.1) + pair N (d' :: ds) u.2 h.2

/-- Every factor divides `N` (and is positive). -/
def Divides (N : ℕ) (ds : List ℕ) : Prop := ∀ d ∈ ds, 0 < d ∧ d ∣ N

theorem Divides.tail {N d : ℕ} {ds : List ℕ} (h : Divides N (d :: ds)) : Divides N ds :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem pair_add_right {N : ℕ} :
    (ds : List ℕ) → Divides N ds → ∀ u h h' : Grp ds,
      pair N ds u (h + h') = pair N ds u h + pair N ds u h'
  | [], _, _, _, _ => by simp [pair]
  | [d], hd, u, h, h' => by
    have : NeZero d := ⟨(hd d List.mem_cons_self).1.ne'⟩
    change embed N d (u * (h + h')) = embed N d (u * h) + embed N d (u * h')
    rw [mul_add, embed_add (hd d List.mem_cons_self).2]
  | d :: d' :: ds, hd, u, h, h' => by
    have : NeZero d := ⟨(hd d List.mem_cons_self).1.ne'⟩
    change embed N d (u.1 * (h.1 + h'.1)) + pair N (d' :: ds) u.2 (h.2 + h'.2) = _
    rw [mul_add, embed_add (hd d List.mem_cons_self).2, pair_add_right (d' :: ds) hd.tail]
    change _ = (embed N d (u.1 * h.1) + pair N (d' :: ds) u.2 h.2) +
      (embed N d (u.1 * h'.1) + pair N (d' :: ds) u.2 h'.2)
    ring

theorem pair_comm {N : ℕ} : (ds : List ℕ) → ∀ u h : Grp ds, pair N ds u h = pair N ds h u
  | [], _, _ => rfl
  | [d], u, h => by
    change embed N d (u * h) = embed N d (h * u)
    rw [mul_comm]
  | d :: d' :: ds, u, h => by
    change embed N d (u.1 * h.1) + pair N (d' :: ds) u.2 h.2 =
      embed N d (h.1 * u.1) + pair N (d' :: ds) h.2 u.2
    rw [mul_comm u.1, pair_comm (d' :: ds)]

theorem pair_add_left {N : ℕ} (ds : List ℕ) (hd : Divides N ds) (u u' h : Grp ds) :
    pair N ds (u + u') h = pair N ds u h + pair N ds u' h := by
  rw [pair_comm, pair_add_right ds hd, pair_comm _ h, pair_comm _ h]

theorem pair_zero_right {N : ℕ} (ds : List ℕ) (hd : Divides N ds) (u : Grp ds) :
    pair N ds u 0 = 0 := by
  have := pair_add_right ds hd u 0 0
  rw [add_zero] at this
  linear_combination -this

theorem pair_neg_right {N : ℕ} (ds : List ℕ) (hd : Divides N ds) (u h : Grp ds) :
    pair N ds u (-h) = -pair N ds u h := by
  have := pair_add_right ds hd u (-h) h
  rw [neg_add_cancel, pair_zero_right ds hd] at this
  linear_combination -this

/-! ### `p^(a−1)` is a multiple of any nonzero element of `ZMod (p^a)` -/

theorem exists_mul_eq_div {p a : ℕ} (hp : p.Prime) {x : ZMod (p ^ a)} (hx : x ≠ 0) :
    ∃ c : ZMod (p ^ a), c * x = ((p ^ a / p : ℕ) : ZMod (p ^ a)) := by
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have : NeZero (p ^ a) := ⟨hpa.ne'⟩
  have hv : x.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  have hlt := ZMod.val_lt x
  set g := Nat.gcd x.val (p ^ a)
  obtain ⟨s, hs, hg⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right x.val (p ^ a))
  have hgx : g ≤ x.val := Nat.le_of_dvd (Nat.pos_of_ne_zero hv) (Nat.gcd_dvd_left _ _)
  have hsa : s < a := by
    by_contra h
    have : p ^ a ≤ p ^ s := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  have hbez : ((g : ℕ) : ZMod (p ^ a)) = x * (Nat.gcdA x.val (p ^ a) : ZMod (p ^ a)) := by
    have e := Nat.gcd_eq_gcd_ab x.val (p ^ a)
    have e2 := congrArg (Int.cast : ℤ → ZMod (p ^ a)) e
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero,
      ZMod.natCast_zmod_val] at e2
    exact e2
  refine ⟨(Nat.gcdA x.val (p ^ a) : ZMod (p ^ a)) * ((p ^ (a - 1 - s) : ℕ) : ZMod (p ^ a)), ?_⟩
  have hdiv1 : p ^ a / p = p ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ hp.pos
  have hdiv : p ^ a / p = p ^ s * p ^ (a - 1 - s) := by
    rw [hdiv1, ← pow_add]
    congr 1
    omega
  rw [hdiv, Nat.cast_mul, ← hg, hbez]
  ring

theorem div_mul_div_eq {p r a : ℕ} (hp : 0 < p) (ha : 1 ≤ a) (hd : p ^ a ∣ r * p) :
    p ^ a / p * (r * p / p ^ a) = r := by
  obtain ⟨m, hm⟩ := hd
  have hpa : 0 < p ^ a := pow_pos hp a
  have h1 : p ^ a / p = p ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ hp
  rw [hm, Nat.mul_div_cancel_left m hpa, h1]
  have : p * (p ^ (a - 1) * m) = p * r := by
    rw [← mul_assoc, ← pow_succ', show a - 1 + 1 = a by omega, ← hm, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hp this

/-- The factors are powers of `p` dividing `N`. -/
def PPowers (p N : ℕ) (ds : List ℕ) : Prop := ∀ d ∈ ds, 0 < d ∧ d ∣ N ∧ ∃ a, d = p ^ a

theorem PPowers.divides {p N : ℕ} {ds : List ℕ} (h : PPowers p N ds) : Divides N ds :=
  fun d hd => ⟨(h d hd).1, (h d hd).2.1⟩

theorem PPowers.tail {p N d : ℕ} {ds : List ℕ} (h : PPowers p N (d :: ds)) : PPowers p N ds :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem exists_embed_eq {p r d : ℕ} (hp : p.Prime) (hd : 0 < d ∧ d ∣ r * p ∧ ∃ a, d = p ^ a)
    {x : ZMod d} (hx : x ≠ 0) : ∃ c : ZMod d, embed (r * p) d (c * x) = (r : ZMod (r * p)) := by
  obtain ⟨hd0, hdN, a, rfl⟩ := hd
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      exact absurd (Subsingleton.elim (α := ZMod 1) x 0) hx
    · exact h
  obtain ⟨c, hc⟩ := exists_mul_eq_div hp hx
  refine ⟨c, ?_⟩
  have : NeZero (p ^ a) := ⟨hd0.ne'⟩
  have hlt : p ^ a / p < p ^ a := Nat.div_lt_self hd0 hp.one_lt
  rw [embed, hc, ZMod.val_cast_of_lt hlt, div_mul_div_eq hp.pos ha hdN]

theorem pair_zero_left {N : ℕ} (ds : List ℕ) (hd : Divides N ds) (h : Grp ds) :
    pair N ds 0 h = 0 := by
  rw [pair_comm, pair_zero_right ds hd]

theorem exists_pair_eq {p r : ℕ} (hp : p.Prime) :
    (ds : List ℕ) → PPowers p (r * p) ds → ∀ h : Grp ds, h ≠ 0 →
      ∃ u, pair (r * p) ds u h = (r : ZMod (r * p))
  | [], _, h, hh => absurd (Subsingleton.elim (α := ZMod 1) h 0) hh
  | [d], hd, h, hh => exists_embed_eq hp (hd d List.mem_cons_self) hh
  | d :: d' :: ds, hd, h, hh => by
    by_cases h1 : h.1 = 0
    · have h2 : (h.2 : Grp (d' :: ds)) ≠ 0 := by
        intro h2
        apply hh
        exact Prod.ext h1 h2
      obtain ⟨u, hu⟩ := exists_pair_eq hp (d' :: ds) hd.tail h.2 h2
      refine ⟨((0 : ZMod d), u), ?_⟩
      change embed (r * p) d (0 * h.1) + pair (r * p) (d' :: ds) u h.2 = _
      rw [zero_mul, embed_zero, zero_add, hu]
    · obtain ⟨c, hc⟩ := exists_embed_eq hp (hd d List.mem_cons_self) h1
      refine ⟨(c, (0 : Grp (d' :: ds))), ?_⟩
      change embed (r * p) d (c * h.1) + pair (r * p) (d' :: ds) 0 h.2 = _
      rw [hc, pair_zero_left _ hd.tail.divides, add_zero]

/-! ### Characters into `A = ℤ[X]/(Ψ)` (`K` trivial) -/

variable {p r : ℕ} [NeZero (r * p)]

/-- `x ↦ ρ^x` on `ZMod (r p)`. -/
noncomputable def rootPow (p r : ℕ) [NeZero (r * p)] :
    Multiplicative (ZMod (r * p)) →* A Unit p r where
  toFun x := AdjoinRoot.root _ ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod _ (root_pow (K := Unit) p r), pow_add]

theorem root_pow_val_add (x y : ZMod (r * p)) :
    AdjoinRoot.root (psi (Rg Unit) p r) ^ (x + y).val =
      AdjoinRoot.root _ ^ x.val * AdjoinRoot.root _ ^ y.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ (root_pow (K := Unit) p r), pow_add]

theorem r_pos (p r : ℕ) [NeZero (r * p)] : 0 < r :=
  Nat.pos_of_ne_zero fun h0 => NeZero.ne (r * p) (by rw [h0, zero_mul])

/-- The pairing with `u` as an additive map. -/
def pairHom (ds : List ℕ) (hd : Divides (r * p) ds) (u : Grp ds) : Grp ds →+ ZMod (r * p) where
  toFun := pair (r * p) ds u
  map_zero' := pair_zero_right ds hd u
  map_add' := pair_add_right ds hd u

/-- The character `h ↦ ρ^⟨u, h⟩` on `ℤ[Grp ds]`. -/
noncomputable def chr (ds : List ℕ) (hd : Divides (r * p) ds) (u : Grp ds) :
    AddMonoidAlgebra ℤ (Grp ds) →ₐ[ℤ] A Unit p r :=
  AddMonoidAlgebra.lift ℤ (A Unit p r) (Grp ds)
    ((rootPow p r).comp (AddMonoidHom.toMultiplicative (pairHom ds hd u)))

theorem chr_single (ds : List ℕ) (hd : Divides (r * p) ds) (u h : Grp ds) (z : ℤ) :
    chr ds hd u (AddMonoidAlgebra.single h z) =
      z • AdjoinRoot.root (psi (Rg Unit) p r) ^ (pair (r * p) ds u h).val := by
  simp [chr, rootPow, pairHom]

theorem chr_ofFun (ds : List ℕ) (hd : Divides (r * p) ds) [Fintype (Grp ds)] (u : Grp ds)
    (Y : Grp ds → ℤ) :
    chr ds hd u (ofFun Y) =
      ∑ h, Y h • AdjoinRoot.root (psi (Rg Unit) p r) ^ (pair (r * p) ds u h).val := by
  rw [ofFun, map_sum]
  exact Finset.sum_congr rfl fun h _ => chr_single ds hd u h (Y h)

omit [NeZero (r * p)] in
/-- `p` is a non-zero-divisor of `A` when `π^φ = p z`. -/
theorem natCast_mul_eq_zero' (hp : p ≠ 0) {M : ℕ} {zc : A Unit p r}
    (hz : (AdjoinRoot.root _ - 1) ^ M = (p : A Unit p r) * zc) {a : A Unit p r}
    (h : (p : A Unit p r) * a = 0) : a = 0 := by
  apply pow_mul_cancel hp M
  rw [hz, mul_zero, mul_assoc, mul_comm zc, ← mul_assoc, h, zero_mul]

theorem sum_pair_eq_zero (hp : p.Prime) (ds : List ℕ) (hd : PPowers p (r * p) ds)
    [Fintype (Grp ds)] {M : ℕ} {zc : A Unit p r}
    (hz : (AdjoinRoot.root _ - 1) ^ M = (p : A Unit p r) * zc) {h : Grp ds} (hh : h ≠ 0) :
    ∑ u : Grp ds, AdjoinRoot.root (psi (Rg Unit) p r) ^ (pair (r * p) ds u h).val = 0 := by
  obtain ⟨u0, hu0⟩ := exists_pair_eq hp ds hd h hh
  set S := ∑ u : Grp ds, AdjoinRoot.root (psi (Rg Unit) p r) ^ (pair (r * p) ds u h).val
  have hrv : (r : ZMod (r * p)).val = r :=
    ZMod.val_cast_of_lt (lt_mul_of_one_lt_right (r_pos p r) hp.one_lt)
  have hshift : S * AdjoinRoot.root _ ^ r = S := by
    rw [Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.addRight u0) _ _ (fun u => ?_)
    simp only [Equiv.coe_addRight]
    rw [pair_add_left ds hd.divides, hu0, root_pow_val_add, hrv]
  have hl : ∀ l : ℕ, S * (AdjoinRoot.root (psi (Rg Unit) p r) ^ r) ^ l = S := by
    intro l
    induction l with
    | zero => rw [pow_zero, mul_one]
    | succ l ih => rw [pow_succ, ← mul_assoc, ih, hshift]
  apply natCast_mul_eq_zero' hp.ne_zero hz
  calc (p : A Unit p r) * S = ∑ l ∈ Finset.range p, S * (AdjoinRoot.root _ ^ r) ^ l := by
        rw [Finset.sum_congr rfl (fun l _ => hl l), Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
    _ = S * ∑ l ∈ Finset.range p, (AdjoinRoot.root _ ^ r) ^ l := by rw [Finset.mul_sum]
    _ = 0 := by rw [sum_root_pow, mul_zero]

/-! ### The norm identity and the sum over all characters -/

theorem chr_neg (ds : List ℕ) (hd : Divides (r * p) ds) [Fintype (Grp ds)] (u : Grp ds)
    (Y : Grp ds → ℤ) :
    chr ds hd u (ofFun fun h => Y (-h)) = conj (K := Unit) p r (chr ds hd u (ofFun Y)) := by
  rw [chr_ofFun, chr_ofFun, map_sum]
  simp only [map_zsmul, map_pow, conj_root, root_pow_neg]
  exact Fintype.sum_equiv (Equiv.neg _) _ _ (fun h => by simp [pair_neg_right ds hd])

theorem chr_univSum (hp : p.Prime) (ds : List ℕ) (hd : PPowers p (r * p) ds) [Fintype (Grp ds)]
    {M : ℕ} {zc : A Unit p r} (hz : (AdjoinRoot.root _ - 1) ^ M = (p : A Unit p r) * zc)
    {u : Grp ds} (hu : u ≠ 0) : chr ds hd.divides u (univSum ℤ (Grp ds)) = 0 := by
  rw [univSum, chr_ofFun]
  simp only [one_smul]
  rw [← sum_pair_eq_zero hp ds hd hz hu]
  exact Finset.sum_congr rfl fun h _ => by rw [pair_comm]

theorem chr_mul_conj (hp : p.Prime) (ds : List ℕ) (hd : PPowers p (r * p) ds) [Fintype (Grp ds)]
    {M : ℕ} {zc : A Unit p r} (hz : (AdjoinRoot.root _ - 1) ^ M = (p : A Unit p r) * zc)
    {u : Grp ds} (hu : u ≠ 0) {Y : Grp ds → ℤ} {n μ : ℤ}
    (hY : ∀ g, ∑ h, Y h * Y (h + g) = (if g = 0 then n else 0) + μ) :
    chr ds hd.divides u (ofFun Y) * conj (K := Unit) p r (chr ds hd.divides u (ofFun Y)) = n := by
  have e := congrArg (chr ds hd.divides u) (ofFun_mul_ofFun_neg_of_autocorr (R := ℤ) hY)
  simp only [Int.cast_id] at e
  rw [map_mul, chr_neg, map_add, map_mul, chr_univSum hp ds hd hz hu, mul_zero, add_zero,
    map_intCast] at e
  exact e

theorem chr_zero (ds : List ℕ) (hd : Divides (r * p) ds) [Fintype (Grp ds)] (Y : Grp ds → ℤ) :
    chr ds hd 0 (ofFun Y) = ((∑ h, Y h : ℤ) : A Unit p r) := by
  rw [chr_ofFun]
  simp [pair_zero_left ds hd]

theorem sum_chr (hp : p.Prime) (ds : List ℕ) (hd : PPowers p (r * p) ds) [Fintype (Grp ds)]
    {M : ℕ} {zc : A Unit p r} (hz : (AdjoinRoot.root _ - 1) ^ M = (p : A Unit p r) * zc)
    (Y : Grp ds → ℤ) :
    ∑ u, chr ds hd.divides u (ofFun Y) = ((Fintype.card (Grp ds) * Y 0 : ℤ) : A Unit p r) := by
  rw [Finset.sum_congr rfl (fun u _ => chr_ofFun ds hd.divides u Y), Finset.sum_comm]
  simp only [← Finset.smul_sum]
  rw [Finset.sum_eq_single (0 : Grp ds)]
  · simp [pair_zero_right ds hd.divides, mul_comm]
  · intro h _ hh
    rw [sum_pair_eq_zero hp ds hd hz hh, smul_zero]
  · simp

/-! ### Integers in `π^(q φ + 1) A` are divisible by `p^(q+1)` -/

omit [NeZero (r * p)] in
theorem dvd_of_eq_root_sub_one_mul (hp : p.Prime) {z : ℤ} {w : A Unit p r}
    (h : (z : A Unit p r) = (AdjoinRoot.root _ - 1) * w) : (p : ℤ) ∣ z := by
  have : Fact p.Prime := ⟨hp⟩
  have e := congrArg (red (K := Unit) p r) h
  rw [map_intCast, map_mul, map_sub, red_root, map_one, sub_self, zero_mul] at e
  have := congrArg (fun x : AddMonoidAlgebra (ZMod p) Unit => x.coeff 0) e
  simp only [AddMonoidAlgebra.intCast_def, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 this

omit [NeZero (r * p)] in
theorem dvd_of_eq_pow_mul (hp : p.Prime) {φ : ℕ} {yc zc : A Unit p r}
    (hpc : (p : A Unit p r) = (AdjoinRoot.root _ - 1) ^ φ * yc)
    (hzc : (AdjoinRoot.root _ - 1) ^ φ = (p : A Unit p r) * zc) :
    ∀ q : ℕ, ∀ z : ℤ, ∀ w : A Unit p r,
      (z : A Unit p r) = (AdjoinRoot.root _ - 1) ^ (q * φ + 1) * w → (p : ℤ) ^ (q + 1) ∣ z := by
  have hcz : zc * yc = 1 := by
    have h1 : (p : A Unit p r) * (1 - zc * yc) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, ← hzc, ← hpc, sub_self]
    have := natCast_mul_eq_zero' hp.ne_zero hzc h1
    linear_combination -this
  intro q
  induction q with
  | zero =>
    intro z w h
    simpa using dvd_of_eq_root_sub_one_mul hp (w := w) (by simpa using h)
  | succ q ih =>
    intro z w h
    obtain ⟨z', rfl⟩ := dvd_of_eq_root_sub_one_mul hp (z := z)
      (w := (AdjoinRoot.root _ - 1) ^ ((q + 1) * φ) * w) (by rw [h]; ring)
    have e1 : (AdjoinRoot.root (psi (Rg Unit) p r) - 1) ^ φ * (yc * (z' : A Unit p r)) =
        (AdjoinRoot.root _ - 1) ^ φ * ((AdjoinRoot.root _ - 1) ^ (q * φ + 1) * w) := by
      rw [← mul_assoc, ← hpc]
      have h' : (p : A Unit p r) * (z' : A Unit p r) =
          (AdjoinRoot.root _ - 1) ^ ((q + 1) * φ + 1) * w := by
        push_cast at h
        exact h
      rw [h']
      ring
    have e2 := pow_mul_cancel hp.ne_zero φ e1
    have e3 : (z' : A Unit p r) = (AdjoinRoot.root _ - 1) ^ (q * φ + 1) * (zc * w) := by
      calc (z' : A Unit p r) = zc * yc * (z' : A Unit p r) := by rw [hcz, one_mul]
        _ = zc * (yc * (z' : A Unit p r)) := by ring
        _ = _ := by rw [e2]; ring
    obtain ⟨m, hm⟩ := ih z' _ e3
    exact ⟨m, by rw [hm, pow_succ]; ring⟩

end SignedDifferenceSets.SylowTrace

namespace SignedDifferenceSets

open SylowTrace Ma

/-- C22, divisibility form: on a quotient `Grp ds` of order `p^t` whose factors are powers of `p`
dividing `r p`, `p^min(t, q+1)` divides the sign sum `s` whenever `2 (q φ + 1) ≤ e φ`,
`φ = (p − 1) r`, `p^e ∣ k − λ`. -/
theorem not_hasSDS_of_sylow {G : Type*} [AddCommGroup G] [Fintype G] (ds : List ℕ)
    [Fintype (Grp ds)] {p r : ℕ} [hp : Fact p.Prime] [NeZero (r * p)] (hd : PPowers p (r * p) ds)
    (φ : G →+ Grp ds) (hφ : Function.Surjective φ) {c : ℕ}
    (hcard : Fintype.card G = c * Fintype.card (Grp ds)) {k : ℕ} {lam : ℤ} {e q t : ℕ}
    (hn : (p : ℤ) ^ e ∣ (k : ℤ) - lam) (hq : 2 * (q * ((p - 1) * r) + 1) ≤ e * ((p - 1) * r))
    (ht : Fintype.card (Grp ds) = p ^ t) {s : ℤ}
    (hs : s ^ 2 = k + lam * ((c : ℤ) * Fintype.card (Grp ds) - 1))
    (hkill : ¬ (p : ℤ) ^ min t (q + 1) ∣ s)
    (hcert : ∀ (S : Type) [CommRing S] (x : S), ∑ l ∈ Finset.range p, (x ^ r) ^ l = 0 →
      ∃ y z : S, (p : S) = (x - 1) ^ ((p - 1) * r) * y ∧ (x - 1) ^ ((p - 1) * r) = p * z) :
    ¬ HasSDS G k lam := by
  intro ⟨D, hD⟩
  have hp0 : p ≠ 0 := hp.out.ne_zero
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
  obtain ⟨yc, zc, hpc, hzc⟩ := hcert (A Unit p r) (AdjoinRoot.root _) sum_root_pow
  obtain ⟨n', hn'⟩ := hn
  have hc1 : ∀ x : Unit, p ^ 1 • x = -x := fun x => Subsingleton.elim _ _
  have hW : ∀ u : Grp ds, ∃ w : A Unit p r, u ≠ 0 →
      chr ds hd.divides u (ofFun Y) = (AdjoinRoot.root _ - 1) ^ (q * ((p - 1) * r) + 1) * w := by
    intro u
    by_cases hu : u = 0
    · exact ⟨0, fun h => absurd hu h⟩
    · have hN : chr ds hd.divides u (ofFun Y) * conj (K := Unit) p r
          (chr ds hd.divides u (ofFun Y)) =
          (AdjoinRoot.root (psi (Rg Unit) p r) - 1) ^ (e * ((p - 1) * r)) * (yc ^ e * n') := by
        rw [chr_mul_conj hp.out ds hd hzc hu hY, hn', Int.cast_mul, Int.cast_pow, Int.cast_natCast,
          hpc, mul_pow, ← pow_mul, mul_comm e]
        ring
      obtain ⟨w, hw⟩ := exists_pow_mul hp0 one_pos hc1 hN _ hq
      exact ⟨w, fun _ => hw⟩
  choose w hw using hW
  have hsum := sum_chr hp.out ds hd hzc Y
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Grp ds)), chr_zero,
    Finset.sum_congr rfl (fun u hu => hw u (Finset.ne_of_mem_erase hu)), ← Finset.mul_sum] at hsum
  have hdiff : (((Fintype.card (Grp ds) * Y 0 - ∑ h, Y h : ℤ)) : A Unit p r) =
      (AdjoinRoot.root _ - 1) ^ (q * ((p - 1) * r) + 1) *
        ∑ u ∈ Finset.univ.erase (0 : Grp ds), w u := by
    push_cast at hsum ⊢
    linear_combination -hsum
  have hdvd := dvd_of_eq_pow_mul hp.out hpc hzc q _ _ hdiff
  have hS : (p : ℤ) ^ min t (q + 1) ∣ ∑ h, Y h := by
    have h1 : (p : ℤ) ^ min t (q + 1) ∣ (Fintype.card (Grp ds) : ℤ) * Y 0 := by
      rw [ht]
      push_cast
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_left _ _)) _
    have h2 : (p : ℤ) ^ min t (q + 1) ∣ (Fintype.card (Grp ds) : ℤ) * Y 0 - ∑ h, Y h :=
      (pow_dvd_pow _ (min_le_right _ _)).trans hdvd
    have := dvd_sub h1 h2
    rwa [sub_sub_cancel] at this
  have hsq := hD.sum_contract_sq φ hφ hcard
  rw [← hs] at hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact hkill (h ▸ hS)
  · exact hkill (by rw [← dvd_neg, ← h]; exact hS)

end SignedDifferenceSets
