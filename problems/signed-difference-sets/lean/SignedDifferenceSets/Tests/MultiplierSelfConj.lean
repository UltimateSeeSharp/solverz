module

public import SignedDifferenceSets.MultiplierSelfConj

/-!
# Tests for C25 (`MultiplierSelfConj.lean`)

`c7 = −3 + 13·[3, 5, 6]` on `ZMod 7` has autocorrelation `338·[g = 0] − 2` (`n = 2·13²`, prime
to 7). `13 ≡ −1` is self-conjugate with `13² ∥ n`, and `2 ∈ ⟨2⟩`, so C25 fixes a translate by
`t = 2`; C10 does not reach `t = 2` (`2 ∉ ⟨13⟩ = {±1}` mod 7). Controls: `c7` itself is fixed by
`x ↦ 2 x`, and no translate is fixed by `x ↦ 3 x`, so the conclusion is not vacuous.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

/-- `−3 + 13·[3, 5, 6]` on `ZMod 7`. -/
def c7 : ZMod 7 → ℤ := fun x => if x = 3 ∨ x = 5 ∨ x = 6 then 10 else -3

theorem c7_autocorr (g : ZMod 7) :
    ∑ h, c7 h * c7 (h + g) = (if g = 0 then 338 else 0) + (-2) := by
  revert g
  decide +kernel

/-- C25 with `t = 2`: some translate of `c7` is fixed by `x ↦ 2 x`. -/
example : ∃ b : ZMod 7, ∀ x, c7 (2 • x + b) = c7 (x + b) := by
  have hcard : Fintype.card (ZMod 7) = 7 := ZMod.card 7
  obtain ⟨b, hb⟩ := exists_translate_fixed_of_autocorr_selfConj c7_autocorr (by norm_num)
    (by rw [hcard, Int.isCoprime_iff_gcd_eq_one]; decide)
  refine ⟨b, hb 2 (by rw [hcard]; decide) fun p hp hpn => ?_⟩
  have h : (p : ℤ) ∣ ((2 * 13 ^ 2 : ℕ) : ℤ) := by simpa using hpn
  rcases (Nat.Prime.dvd_mul hp).1 (Int.natCast_dvd_natCast.1 h) with h2 | h13
  · left
    refine ⟨1, fun x => ?_⟩
    rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2, pow_one]
  · right
    rw [(Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h13)]
    exact ⟨⟨1, one_pos, by decide +kernel⟩, 1, by norm_num, by norm_num⟩

-- The conclusion holds with `b = 0`.
example : ∀ x : ZMod 7, c7 (2 • x) = c7 x := by decide +kernel

-- A control: no translate is fixed by `x ↦ 3 x` (`3 ∉ ⟨2⟩` mod 7).
example : ∀ b : ZMod 7, ∃ x : ZMod 7, c7 (3 • x + b) ≠ c7 (x + b) := by decide +kernel

/-- C10 does not reach `t = 2`: `13^f ≡ ±1` mod 7, never `2`. -/
example (f : ℕ) : ¬ ∀ x : ZMod 7, 2 • x = 13 ^ f • x := by
  have h1 : (13 : ZMod 7) ^ f = 1 ∨ (13 : ZMod 7) ^ f = -1 := by
    induction f with
    | zero => exact Or.inl (pow_zero _)
    | succ m ih => rcases ih with h | h <;> rw [pow_succ, h] <;> decide +kernel
  intro h
  have h2 := h 1
  rw [nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one] at h2
  push_cast at h2
  rcases h1 with h1 | h1 <;> rw [h1] at h2 <;> revert h2 <;> decide +kernel

end SignedDifferenceSets.Tests
