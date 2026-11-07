module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import SignedDifferenceSets.LinearMaps
public import SignedDifferenceSets.MultiplierWitt
public import SignedDifferenceSets.SelfConjugacyCheck

/-!
# Field descent without ramification (C27)

On a cyclic quotient `ZMod m` with `m` prime to `n = k − λ`, C10 gives coset sums `Y` (fibres of
size `c`) fixed by every multiplier. If each `t = 1 + F u` (`F d = m`, `u < d`) is one, every
character `χ_a`, `a` a unit, sees only the points `F h = 0` (`chi_eq_chi_restrict`), and Parseval
gives `φ(m) n ≤ m F c²` (`IsSDS.totient_mul_le`): Schmidt's field-descent bound for `n` prime to
`m`, its `F` read off the multipliers. `DescentRowCert` checks it on a row.
-/

@[expose] public section

open Finset ComplexConjugate

namespace SignedDifferenceSets

namespace Descent

variable {m : ℕ} [NeZero m]

/-- `χ_a(f) = ∑ f(h) ζ^(a h)`, `ζ = e^(2πi/m)`. -/
noncomputable def chi (a : ZMod m) (f : ZMod m → ℤ) : ℂ :=
  ∑ h, (f h : ℂ) * ZMod.stdAddChar (a * h)

theorem sum_stdAddChar_mul (x : ZMod m) :
    ∑ a : ZMod m, ZMod.stdAddChar (a * x) = if x = 0 then (m : ℂ) else 0 := by
  rw [AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar m), ZMod.card]
  split_ifs <;> simp

/-- `|χ_a(f)|²` through the autocorrelation of `f`. -/
theorem chi_mul_conj (a : ZMod m) (f : ZMod m → ℤ) :
    chi a f * conj (chi a f) =
      ∑ g, ((∑ h, f h * f (h + g) : ℤ) : ℂ) * ZMod.stdAddChar (a * g) := by
  have hc : conj (chi a f) = ∑ h, (f h : ℂ) * ZMod.stdAddChar (-(a * h)) := by
    simp only [chi, map_sum, map_mul, map_intCast, AddChar.map_neg_eq_conj]
  rw [hc, chi, Finset.sum_mul_sum, Finset.sum_comm]
  simp only [Int.cast_sum, Int.cast_mul, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun x => ?_
  have hx : y + (x - y) = x := by abel
  have hψ : (ZMod.stdAddChar (a * x) : ℂ) * ZMod.stdAddChar (-(a * y)) =
      ZMod.stdAddChar (a * (x - y)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [Equiv.subRight_apply, hx, ← hψ]
  ring

/-- `|χ_a(f)|² = n` at every `a ≠ 0` when `f` has autocorrelation `n [g = 0] + μ`. -/
theorem chi_mul_conj_eq {f : ZMod m → ℤ} {n μ : ℤ}
    (hf : ∀ g, ∑ h, f h * f (h + g) = (if g = 0 then n else 0) + μ) {a : ZMod m} (ha : a ≠ 0) :
    chi a f * conj (chi a f) = n := by
  have hz : ∑ g : ZMod m, (ZMod.stdAddChar (a * g) : ℂ) = 0 := by
    simp_rw [mul_comm a]
    rw [sum_stdAddChar_mul, ite_eq_right ha]
  rw [chi_mul_conj]
  simp only [hf, Int.cast_add, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hz, mul_zero,
    add_zero, Int.cast_ite, Int.cast_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, AddChar.map_zero_eq_one, mul_one]

/-- Parseval: `∑_a |χ_a(f)|² = m ∑ f²`. -/
theorem sum_chi_mul_conj (f : ZMod m → ℤ) :
    ∑ a, chi a f * conj (chi a f) = (m : ℂ) * ((∑ h, f h * f h : ℤ) : ℂ) := by
  simp only [chi_mul_conj]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_stdAddChar_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, add_zero]
  ring

/-- `f` with every point off `F h = 0` set to `0`. -/
def restrict (F : ℕ) (f : ZMod m → ℤ) (h : ZMod m) : ℤ := if F • h = 0 then f h else 0

/-- The descent: if every `1 + F u` (`u < d`, `F d = m`) is a unit fixing `f`, a unit `a` sees
only the points `F h = 0`. -/
theorem chi_eq_chi_restrict {f : ZMod m → ℤ} {F d : ℕ} (hFd : F * d = m) (hd : 0 < d)
    (hunit : ∀ u < d, IsUnit ((1 + F * u : ℕ) : ZMod m))
    (hfix : ∀ u < d, ∀ h, f (((1 + F * u : ℕ) : ZMod m) * h) = f h)
    {a : ZMod m} (ha : IsUnit a) : chi a f = chi a (restrict F f) := by
  have hstep (u : ℕ) (hu : u < d) : chi a f = ∑ h, (f h : ℂ) * ZMod.stdAddChar (a * h) *
      ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u := by
    obtain ⟨U, hU⟩ := hunit u hu
    rw [chi]
    symm
    refine Fintype.sum_bijective (fun h => (U : ZMod m) * h) (Units.mulLeft_bijective U) _ _
      fun h => ?_
    rw [hU, hfix u hu h]
    have hψ : ZMod.stdAddChar (a * h) * ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u =
        (ZMod.stdAddChar (a * (((1 + F * u : ℕ) : ZMod m) * h)) : ℂ) := by
      rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
      congr 1
      rw [nsmul_eq_mul]
      push_cast
      ring
    rw [← hψ]
    ring
  have hsum : (d : ℂ) * chi a f = ∑ h, (f h : ℂ) * ZMod.stdAddChar (a * h) *
      ∑ u ∈ range d, ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u := by
    calc (d : ℂ) * chi a f = ∑ _u ∈ range d, chi a f := by simp
      _ = ∑ u ∈ range d, ∑ h, (f h : ℂ) * ZMod.stdAddChar (a * h) *
            ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u :=
          Finset.sum_congr rfl fun u hu => hstep u (Finset.mem_range.1 hu)
      _ = _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  have hm0 : ((F * d : ℕ) : ZMod m) = 0 := by rw [hFd, ZMod.natCast_self]
  have hgeom (h : ZMod m) : ∑ u ∈ range d, ZMod.stdAddChar (a * (F : ZMod m) * h) ^ u =
      if F • h = 0 then (d : ℂ) else 0 := by
    rw [nsmul_eq_mul]
    split_ifs with hF
    · simp [mul_assoc, hF]
    · have hw : ZMod.stdAddChar (a * (F : ZMod m) * h) ≠ (1 : ℂ) := by
        rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := m)), Ne,
          ZMod.injective_stdAddChar.eq_iff, mul_assoc]
        exact fun h0 => hF ((ha.mul_right_eq_zero).1 h0)
      have hw1 : ZMod.stdAddChar (a * (F : ZMod m) * h) ^ d = (1 : ℂ) := by
        have hx : (d : ZMod m) * (a * F * h) = ((F * d : ℕ) : ZMod m) * (a * h) := by
          push_cast
          ring
        rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hx, hm0, zero_mul,
          AddChar.map_zero_eq_one]
      rw [geom_sum_eq hw, hw1, sub_self, zero_div]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  apply mul_left_cancel₀ hd0
  rw [hsum, chi, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [hgeom h, restrict]
  split_ifs
  · ring
  · simp

/-- The bound: with `f` as in `chi_eq_chi_restrict`, autocorrelation `n [g = 0] + μ` and
`|f| ≤ c`, `φ(m) n ≤ m F c²`. -/
theorem totient_mul_le {f : ZMod m → ℤ} {n μ : ℤ} {c F d : ℕ} (hm : 1 < m)
    (hf : ∀ g, ∑ h, f h * f (h + g) = (if g = 0 then n else 0) + μ) (hc : ∀ h, |f h| ≤ c)
    (hFd : F * d = m) (hunit : ∀ u < d, IsUnit ((1 + F * u : ℕ) : ZMod m))
    (hfix : ∀ u < d, ∀ h, f (((1 + F * u : ℕ) : ZMod m) * h) = f h) :
    (Nat.totient m : ℤ) * n ≤ m * F * c ^ 2 := by
  classical
  have : Fact (1 < m) := ⟨hm⟩
  have hd : 0 < d := Nat.pos_of_ne_zero fun h0 => by subst h0; omega
  have hF : 0 < F := Nat.pos_of_ne_zero fun h0 => by subst h0; omega
  set g := restrict F f with hg
  -- each unit sees `n`
  have hunits (a : (ZMod m)ˣ) : Complex.normSq (chi (a : ZMod m) g) = n := by
    have h1 := chi_mul_conj_eq hf (a.ne_zero)
    rw [chi_eq_chi_restrict hFd hd hunit hfix a.isUnit, Complex.mul_conj] at h1
    exact_mod_cast h1
  -- Parseval for `g`
  have hpars : ∑ a, Complex.normSq (chi a g) = (m : ℝ) * ((∑ h, g h * g h : ℤ) : ℝ) := by
    have h1 := sum_chi_mul_conj (m := m) g
    simp only [Complex.mul_conj] at h1
    exact_mod_cast h1
  -- `g` lives on at most `F` points, each at most `c²`
  have hcard : (univ.filter fun h : ZMod m => F • h = 0).card ≤ F := by
    convert IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod m) hF
  have hgsq : ∑ h, g h * g h ≤ F * c ^ 2 := by
    calc ∑ h, g h * g h = ∑ h ∈ univ.filter fun h : ZMod m => F • h = 0, f h * f h := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [hg, restrict]
          split_ifs <;> simp
      _ ≤ ∑ _h ∈ univ.filter fun h : ZMod m => F • h = 0, (c : ℤ) ^ 2 := by
          refine Finset.sum_le_sum fun h _ => ?_
          rw [← sq, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hc h) 2
      _ ≤ F * c ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          gcongr
  have hle : ∑ a : (ZMod m)ˣ, Complex.normSq (chi (a : ZMod m) g) ≤
      ∑ a, Complex.normSq (chi a g) := by
    rw [← Finset.sum_image (s := univ) (g := ((↑) : (ZMod m)ˣ → ZMod m))
      (f := fun x => Complex.normSq (chi x g)) (fun a _ b _ h => Units.ext h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => Complex.normSq_nonneg _
  simp only [hunits, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient,
    nsmul_eq_mul] at hle
  rw [hpars] at hle
  have hgsq' : ((∑ h, g h * g h : ℤ) : ℝ) ≤ F * c ^ 2 := by exact_mod_cast hgsq
  have hfin : (Nat.totient m : ℝ) * n ≤ m * F * c ^ 2 := by
    calc (Nat.totient m : ℝ) * n ≤ m * ((∑ h, g h * g h : ℤ) : ℝ) := hle
      _ ≤ m * (F * c ^ 2) := by gcongr
      _ = m * F * c ^ 2 := by ring
  exact_mod_cast hfin

end Descent

open Descent

/-- C27: an SDS with a cyclic quotient `ZMod m` (fibres of size `c`), `m` prime to `n = k − λ`,
and every `1 + F u` (`F d = m`, `u < d`) a unit congruent to a power of each prime `p ∣ n`, has
`φ(m) n ≤ m F c²`. -/
theorem IsSDS.totient_mul_le {G : Type*} [AddCommGroup G] [Fintype G] {k : ℕ}
    {lam : ℤ} {D : G → SignType} (hD : IsSDS k lam D) {m c F d : ℕ} [NeZero m] (hm : 1 < m)
    (φ : G →+ ZMod m) (hφ : Function.Surjective φ) (hcard : Fintype.card G = c * m)
    (hn0 : (k : ℤ) - lam ≠ 0) (hcop : IsCoprime (m : ℤ) ((k : ℤ) - lam)) (hFd : F * d = m)
    (hmul : ∀ u < d, Nat.Coprime (1 + F * u) m ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam →
      ∃ e : ℕ, (1 + F * u) % m = p ^ e % m) :
    (Nat.totient m : ℤ) * ((k : ℤ) - lam) ≤ m * F * c ^ 2 := by
  have hcardH : Fintype.card G = c * Fintype.card (ZMod m) := by rw [ZMod.card]; exact hcard
  obtain ⟨b, hb⟩ := hD.exists_translate_fixed_contract' φ hφ hcardH hn0 (by rwa [ZMod.card])
  have hA : ∀ g, ∑ h, contract φ D h * contract φ D (h + g) =
      (if g = 0 then (k : ℤ) - lam else 0) + lam * c := by
    intro g
    by_cases hg : g = 0
    · subst hg
      simp only [add_zero, ite_true]
      rw [hD.contract_sq φ, card_fibre_eq hφ hcardH, Nat.cast_sub (one_le_of_card hcardH),
        Nat.cast_one]
      ring
    · rw [hD.contract_autocorr φ g hg, card_fibre_eq hφ hcardH, ite_eq_right hg, zero_add]
  refine Descent.totient_mul_le (f := fun h => contract φ D (h + b)) hm
    (autocorr_translate hA b) (fun h => ?_) hFd
    (fun u hu => (ZMod.isUnit_iff_coprime _ _).2 (hmul u hu).1) (fun u hu h => ?_)
  · have := abs_contract_le φ D (h + b)
    rwa [card_fibre_eq hφ hcardH] at this
  · have ht : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ (k : ℤ) - lam →
        ∃ e : ℕ, ∀ x : ZMod m, (1 + F * u) • x = p ^ e • x := by
      intro p hp hpn
      obtain ⟨e, he⟩ := (hmul u hu).2 p hp hpn
      exact ⟨e, fun x => by rw [nsmul_eq_mul, nsmul_eq_mul,
        (ZMod.natCast_eq_natCast_iff' _ _ _).2 he]⟩
    have := hb (1 + F * u) (by rw [ZMod.card]; exact (hmul u hu).1) ht h
    rwa [nsmul_eq_mul] at this

/-- A C27 certificate: the quotient `ZMod m` as the form `A` with a preimage `P` of `1`, and `F`. -/
structure DescentRowCert where
  m : ℕ
  F : ℕ
  A : List ℕ
  P : List ℕ
  deriving DecidableEq

/-- C27's hypotheses on the row (`n = k − λ`, `c = v / m`; a prime `p ∣ n` is one with no divisor
in `[2, p)`) and the kill `m F c² < φ(m) n`. -/
def DescentRowCert.Kills (w : Row) (c : DescentRowCert) : Prop :=
  (∀ x ∈ w.ms, 0 < x) ∧ 1 < c.m ∧ c.m ∣ w.ms.prod ∧ MapOk w.ms [c.m] [c.A] ∧
    SurjCert w.ms [c.m] [c.A] [c.P] ∧ c.F ∣ c.m ∧ 0 < (w.k : ℤ) - w.lam ∧
    Nat.Coprime c.m (w.k - w.lam).toNat ∧
    (∀ u ∈ List.range (c.m / c.F), Nat.Coprime (1 + c.F * u) c.m ∧
      ∀ p ∈ List.range ((w.k - w.lam).toNat + 1), 2 ≤ p → p ∣ (w.k - w.lam).toNat →
        (∀ q ∈ List.range p, 2 ≤ q → p % q ≠ 0) →
          ∃ e ∈ List.range c.m, (1 + c.F * u) % c.m = p ^ e % c.m) ∧
    c.m * c.F * (w.ms.prod / c.m) ^ 2 < Nat.totient c.m * (w.k - w.lam).toNat

instance (w : Row) (c : DescentRowCert) : Decidable (c.Kills w) := by
  unfold DescentRowCert.Kills; infer_instance

/-- A killed row has no SDS. -/
theorem DescentRowCert.not_hasSDS {w : Row} {c : DescentRowCert} (h : c.Kills w)
    (inst : Fintype (Grp w.ms)) : ¬ @HasSDS (Grp w.ms) _ inst w.k w.lam := by
  obtain ⟨-, hm, hmv, hmap, hsurj, hFm, hn, hcop, hmul, hkill⟩ := h
  rintro ⟨D, hD⟩
  have : NeZero c.m := ⟨by omega⟩
  have hnZ : (w.k : ℤ) - w.lam = ((w.k - w.lam).toNat : ℤ) := (Int.toNat_of_nonneg hn.le).symm
  let φ : Grp w.ms →+ ZMod c.m := linMap w.ms [c.m] [c.A] hmap
  have hφ : Function.Surjective φ := linMap_surjective hmap hsurj
  have hcard : Fintype.card (Grp w.ms) = w.ms.prod / c.m * c.m := by
    rw [Grp.card_eq, Nat.div_mul_cancel hmv]
  have key := hD.totient_mul_le hm φ hφ hcard (by omega)
    (by rw [hnZ]; exact Nat.isCoprime_iff_coprime.2 hcop) (Nat.mul_div_cancel' hFm)
    (fun u hu => ⟨(hmul u (List.mem_range.2 hu)).1, fun p hp hpn => by
      rw [hnZ] at hpn
      have hpn' : p ∣ (w.k - w.lam).toNat := Int.natCast_dvd_natCast.1 hpn
      have hpos : 0 < (w.k - w.lam).toNat := by omega
      obtain ⟨e, -, he⟩ := (hmul u (List.mem_range.2 hu)).2 p
        (List.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd hpos hpn'))) hp.two_le hpn'
        (fun q hq hq2 hpq => by
          rcases hp.eq_one_or_self_of_dvd q (Nat.dvd_of_mod_eq_zero hpq) with h1 | h1
          · omega
          · exact absurd (List.mem_range.1 hq) (by omega))
      exact ⟨e, he⟩⟩)
  rw [hnZ] at key
  have hle : Nat.totient c.m * (w.k - w.lam).toNat ≤ c.m * c.F * (w.ms.prod / c.m) ^ 2 := by
    exact_mod_cast key
  exact absurd hle (not_le.2 hkill)

end SignedDifferenceSets
