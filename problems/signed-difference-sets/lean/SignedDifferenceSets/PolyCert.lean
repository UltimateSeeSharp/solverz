module

public import Mathlib

/-!
# Integer polynomials the kernel computes, and C21's cyclotomic certificate

A polynomial is its list of integer coefficients, constant term first. `evalL x` evaluates one in
any commutative ring; `addL`, `smulL`, `mulL`, `powL`, `monoL` (`X^n`) and `geomL` (`∑_{l<n} q^l`)
compute on lists, and `evalL` respects each of them.

`MaCert p r f g u w` checks, with `N = (p − 1) r` and `Ψ = ∑_{l<p} X^(r l)`,
`(X − 1)^N f + Ψ g = p` and `(X − 1)^N = p u + Ψ w` coefficient by coefficient.
`MaCert.cycloFacts` turns it into `CycloFacts p r`, `MaRule`'s last hypothesis: wherever
`Ψ(x) = 0`, `p = (x − 1)^N f(x)` and `(x − 1)^N = p u(x)`. Coefficients too long for one line
are written as `ofLimbs` of base-`10^80` digits. `CycloFacts.mul` lifts the facts from `r` to
`p r` (`p` prime, `(p − 1) r ≥ 2`), so certificates are needed only at small `r`.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- `[a₀, a₁, …]` at `x`: `a₀ + x (a₁ + x (…))`. -/
def evalL {S : Type*} [CommRing S] (x : S) : List ℤ → S
  | [] => 0
  | a :: as => a + x * evalL x as

/-- Sum, coefficient by coefficient. -/
def addL : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addL as bs

/-- Product with a constant. -/
def smulL (a : ℤ) : List ℤ → List ℤ
  | [] => []
  | b :: bs => (a * b) :: smulL a bs

/-- Product. -/
def mulL : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: as, bs => addL (smulL a bs) (0 :: mulL as bs)

/-- `n`-th power. -/
def powL (a : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => mulL (powL a n) a

/-- `X^n`. -/
def monoL : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => 0 :: monoL n

/-- `∑_{l<n} q^l`, by Horner's rule. -/
def geomL (q : List ℤ) : ℕ → List ℤ
  | 0 => []
  | n + 1 => addL [1] (mulL q (geomL q n))

section Eval

variable {S : Type*} [CommRing S] (x : S)

@[simp] theorem evalL_nil : evalL x [] = 0 := rfl

@[simp] theorem evalL_cons (a : ℤ) (as : List ℤ) : evalL x (a :: as) = a + x * evalL x as := rfl

theorem evalL_addL : ∀ as bs : List ℤ, evalL x (addL as bs) = evalL x as + evalL x bs
  | [], bs => by simp [addL]
  | a :: as, [] => by simp [addL]
  | a :: as, b :: bs => by
    simp only [addL, evalL_cons, evalL_addL as bs, Int.cast_add]
    ring

theorem evalL_smulL (a : ℤ) : ∀ bs : List ℤ, evalL x (smulL a bs) = a * evalL x bs
  | [] => by simp [smulL]
  | b :: bs => by
    simp only [smulL, evalL_cons, evalL_smulL a bs, Int.cast_mul]
    ring

theorem evalL_mulL : ∀ as bs : List ℤ, evalL x (mulL as bs) = evalL x as * evalL x bs
  | [], bs => by simp [mulL]
  | a :: as, bs => by
    simp only [mulL, evalL_addL, evalL_smulL, evalL_cons, evalL_mulL as bs, Int.cast_zero]
    ring

theorem evalL_powL (a : List ℤ) : ∀ n : ℕ, evalL x (powL a n) = evalL x a ^ n
  | 0 => by simp [powL]
  | n + 1 => by rw [powL, evalL_mulL, evalL_powL a n, pow_succ]

theorem evalL_monoL : ∀ n : ℕ, evalL x (monoL n) = x ^ n
  | 0 => by simp [monoL]
  | n + 1 => by rw [monoL, evalL_cons, evalL_monoL n, pow_succ']; simp

theorem evalL_geomL (q : List ℤ) :
    ∀ n : ℕ, evalL x (geomL q n) = ∑ l ∈ Finset.range n, evalL x q ^ l
  | 0 => by simp [geomL]
  | n + 1 => by
    rw [geomL, evalL_addL, evalL_mulL, evalL_geomL q n, geom_sum_succ]
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_one]
    ring

theorem evalL_eq_zero : ∀ as : List ℤ, (∀ a ∈ as, a = 0) → evalL x as = 0
  | [], _ => rfl
  | a :: as, h => by
    rw [evalL_cons, h a List.mem_cons_self,
      evalL_eq_zero as fun b hb => h b (List.mem_cons_of_mem _ hb)]
    simp

end Eval

/-- The number with base-`10^80` digits `ds`, most significant first: long literals in lines
of at most 100 characters. -/
def ofLimbs (ds : List ℕ) : ℕ := ds.foldl (fun a d => a * 10 ^ 80 + d) 0

/-- `Ψ = ∑_{l<p} X^(r l)`. -/
def psiL (p r : ℕ) : List ℤ := geomL (monoL r) p

/-- `(X − 1)^((p − 1) r)`. -/
def piL (p r : ℕ) : List ℤ := powL [-1, 1] ((p - 1) * r)

/-- C21's cyclotomic certificate at `(p, r)`: `(X − 1)^N f + Ψ g − p` and
`(X − 1)^N − (p u + Ψ w)` have only zero coefficients. -/
def MaCert (p r : ℕ) (f g u w : List ℤ) : Prop :=
  (∀ a ∈ addL (addL (mulL (piL p r) f) (mulL (psiL p r) g)) [-(p : ℤ)], a = 0) ∧
    ∀ a ∈ addL (piL p r) (smulL (-1) (addL (smulL p u) (mulL (psiL p r) w))), a = 0

instance (p r : ℕ) (f g u w : List ℤ) : Decidable (MaCert p r f g u w) := by
  unfold MaCert; infer_instance

/-- The cyclotomic facts `MaRule` takes at `(p, r)`. -/
def CycloFacts (p r : ℕ) : Prop :=
  ∀ (S : Type) [CommRing S] (x : S), ∑ l ∈ Finset.range p, (x ^ r) ^ l = 0 →
    ∃ y z : S, (p : S) = (x - 1) ^ ((p - 1) * r) * y ∧ (x - 1) ^ ((p - 1) * r) = p * z

/-- A certificate gives the facts, with `y = f(x)` and `z = u(x)`. -/
theorem MaCert.cycloFacts {p r : ℕ} {f g u w : List ℤ} (h : MaCert p r f g u w) :
    CycloFacts p r := by
  intro S _ x hx
  have hpsi : evalL x (psiL p r) = 0 := by rw [psiL, evalL_geomL, evalL_monoL]; exact hx
  have hpi : evalL x (piL p r) = (x - 1) ^ ((p - 1) * r) := by
    rw [piL, evalL_powL]
    simp only [evalL_cons, evalL_nil, mul_zero, add_zero, Int.cast_neg, Int.cast_one, mul_one]
    ring
  refine ⟨evalL x f, evalL x u, ?_, ?_⟩
  · have h1 := evalL_eq_zero x _ h.1
    simp only [evalL_addL, evalL_mulL, hpsi, hpi, evalL_cons, evalL_nil] at h1
    push_cast at h1
    linear_combination -h1
  · have h2 := evalL_eq_zero x _ h.2
    simp only [evalL_addL, evalL_mulL, evalL_smulL, hpsi, hpi] at h2
    push_cast at h2
    linear_combination h2

/-- From `r` to `p r`, through `x' = x^p` and `(x − 1)^p = (x^p − 1) + p c`: with `t = x − 1`,
`s = x^p − 1`, `n = (p − 1) r ≥ 2`, `t ∣ s` and `t^(p n) = s^n + p c Q` with `t ∣ Q`, so
`p (1 − t u) = t^(p n) y'`, and a geometric sum in `t u` gives `p ∈ t^(p n) S`. -/
theorem CycloFacts.mul {p r : ℕ} (hp : p.Prime) (hn : 2 ≤ (p - 1) * r) (h : CycloFacts p r) :
    CycloFacts p (p * r) := by
  intro S _ x hx
  obtain ⟨y', z', hy', hz'⟩ := h S (x ^ p) (by rw [← pow_mul]; exact hx)
  obtain ⟨c, hc⟩ : ∃ c : S, (x - 1) ^ p = (x ^ p - 1) + p * c := by
    obtain ⟨w, hw⟩ := exists_add_pow_prime_eq hp x (-1)
    rw [← sub_eq_add_neg] at hw
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact ⟨1 - x * w, by rw [hw]; push_cast; ring⟩
    · exact ⟨-(x * w), by rw [hw, hodd.neg_one_pow]; ring⟩
  have hts : x - 1 ∣ x ^ p - 1 := ⟨_, (mul_geom_sum x p).symm⟩
  rw [show (p - 1) * (p * r) = p * ((p - 1) * r) by ring]
  generalize (p - 1) * r = n at hn hy' hz' ⊢
  generalize x - 1 = t at hc hts ⊢
  generalize x ^ p - 1 = s at hc hts hy' hz' ⊢
  obtain ⟨Q, hQ, v, hv⟩ : ∃ Q : S, (t ^ p) ^ n = s ^ n + p * c * Q ∧ t ∣ Q := by
    refine ⟨∑ i ∈ Finset.range n, (t ^ p) ^ i * s ^ (n - 1 - i), ?_, Finset.dvd_sum fun i _ => ?_⟩
    · linear_combination -geom_sum₂_mul (t ^ p) s n +
        (∑ i ∈ Finset.range n, (t ^ p) ^ i * s ^ (n - 1 - i)) * hc
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact (dvd_pow hts (by omega)).mul_left _
      · exact (dvd_pow (dvd_pow_self t hp.ne_zero) hi0.ne').mul_right _
  set u := -(c * v * y') with hu
  have hG := mul_neg_geom_sum (t * u) (p * n)
  refine ⟨y' * ∑ i ∈ Finset.range (p * n), (t * u) ^ i + p * u ^ (p * n), z' + c * Q, ?_, ?_⟩
  · linear_combination (∑ i ∈ Finset.range (p * n), (t * u) ^ i) * hy' -
      p * c * y' * (∑ i ∈ Finset.range (p * n), (t * u) ^ i) * hv -
      y' * (∑ i ∈ Finset.range (p * n), (t * u) ^ i) * hQ - p * hG -
      p * t * (∑ i ∈ Finset.range (p * n), (t * u) ^ i) * hu
  · rw [pow_mul, hQ, hz']
    ring

end SignedDifferenceSets
