module

public import SignedDifferenceSets.MultiplierWitt
public import SignedDifferenceSets.SetCheck

/-!
# Tests for C9 for every `n` (`MultiplierWitt.lean`)

The Singer (91, 10, 1) difference set `{0, 1, 3, 9, 27, 49, 56, 61, 77, 81}` in ℤ₉₁ (all signs
`+`) has `n = 9`, not squarefree, and prime to `v = 91`, so C15 does not apply to it.
`IsSDS.exists_translate_fixed'` gives a translate fixed by the multiplier `t = 3` (`3 ≡ 3¹`); the
set itself is one (checked directly).
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

/-- The Singer set's elements, as bits over the element numbers of `Indexed`. -/
def singerPlus : ℕ := 2 ^ 0 + 2 ^ 1 + 2 ^ 3 + 2 ^ 9 + 2 ^ 27 + 2 ^ 49 + 2 ^ 56 + 2 ^ 61 + 2 ^ 77 +
  2 ^ 81

/-- The Singer (91, 10, 1) difference set in ℤ₉₁. -/
def singer91 : ZMod 91 → SignType :=
  fun x => ofMasks singerPlus 0 (Indexed.equiv x)

theorem singer91_isSDS : IsSDS 10 1 singer91 :=
  isSDS_of_checkSet (G := ZMod 91) (P := singerPlus) (N := 0) (by decide +kernel)

/-- C9 for `n = 9`: some translate of the Singer set is fixed by `x ↦ 3 x`. -/
example : ∃ a : ZMod 91, ∀ x, singer91 (3 • x + a) = singer91 (x + a) := by
  have hcard : Fintype.card (ZMod 91) = 91 := ZMod.card 91
  obtain ⟨a, ha⟩ := singer91_isSDS.exists_translate_fixed' (by norm_num)
    (by rw [hcard, Int.isCoprime_iff_gcd_eq_one]; decide)
  refine ⟨a, ha 3 (by rw [hcard]; decide) fun p hp hpn => ⟨1, fun x => ?_⟩⟩
  have h9 : (p : ℤ) ∣ ((3 ^ 2 : ℕ) : ℤ) := by simpa using hpn
  have h3 : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
      (hp.dvd_of_dvd_pow (Int.natCast_dvd_natCast.1 h9))
  rw [h3, pow_one]

-- The conclusion holds with `a = 0`: the set is fixed by `x ↦ 3 x`.
example : ∀ x : ZMod 91, singer91 (3 • x) = singer91 x := by decide +kernel

-- A control: `x ↦ 2 x` (2 is not a multiplier, `2 ∉ ⟨3⟩` mod 91) moves every translate.
example : ∀ a : ZMod 91, ∃ x : ZMod 91, singer91 (2 • x + a) ≠ singer91 (x + a) := by
  decide +kernel

end SignedDifferenceSets.Tests
