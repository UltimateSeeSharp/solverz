import SignedDifferenceSets.Multiplier
import SignedDifferenceSets.Check

open SignedDifferenceSets


-- Non-vacuity: the (7,3,1) difference set {0,1,3} in Z7, n = 2, t = 2.
def d731 : ZMod 7 → SignType := fun x => ![1, 1, 0, 1, 0, 0, 0] x

theorem d731_sds : IsSDS 3 1 d731 := by decide

theorem d731_fixed : ∃ a : ZMod 7, ∀ x, d731 (2 • x + a) = d731 (x + a) := by
  have h2 : ((3 : ℕ) : ℤ) - 1 = 2 := by norm_num
  have hsq : Squarefree (((3 : ℕ) : ℤ) - 1) := by rw [h2]; exact Int.prime_two.squarefree
  have hcop : IsCoprime (Fintype.card (ZMod 7) : ℤ) (((3 : ℕ) : ℤ) - 1) := by
    rw [h2, ZMod.card]; exact ⟨1, -3, by norm_num⟩
  obtain ⟨a, ha⟩ := d731_sds.exists_translate_fixed hsq hcop
  refine ⟨a, ha 2 (by rw [ZMod.card]; norm_num) ?_⟩
  intro p hp hpd
  rw [h2] at hpd
  have hp2 : p = 2 := by
    have : p ∣ 2 := by exact_mod_cast hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this
  exact ⟨1, fun x => by simp [hp2]⟩

-- The fixed translate is a = 6 here? Sanity: which a works, by decide (independent of the theorem).
example : ∀ x : ZMod 7, d731 (2 • x + 6) = d731 (x + 6) := by decide

-- n = 1 (no prime divides n): every t prime to v must then fix one translate.
-- (3,2,1) in Z3: D = {0,1}; t = 2 is the only nontrivial unit.
def d321 : ZMod 3 → SignType := fun x => ![1, 1, 0] x
theorem d321_sds : IsSDS 2 1 d321 := by decide
theorem d321_fixed : ∃ a : ZMod 3, ∀ x, d321 (2 • x + a) = d321 (x + a) := by
  have h1 : ((2 : ℕ) : ℤ) - 1 = 1 := by norm_num
  obtain ⟨a, ha⟩ := d321_sds.exists_translate_fixed (by rw [h1]; exact squarefree_one)
    (by rw [h1]; exact isCoprime_one_right)
  refine ⟨a, ha 2 (by rw [ZMod.card]; norm_num) ?_⟩
  intro p hp hpd
  rw [h1] at hpd
  exact absurd (Int.eq_one_of_dvd_one (by positivity) hpd) (by exact_mod_cast hp.one_lt.ne')

#print axioms d731_fixed
#print axioms d321_fixed
