module

public import Mathlib

/-!
# Loops the kernel evaluates

Sums, `∀ i < n` tests and integer ranges by structural recursion, so `decide +kernel`
evaluates them (well-founded recursion does not reduce), each with its specification.
Tests stop at the first failure.
-/

@[expose] public section

namespace SignedDifferenceSets

/-- `f 0 + ⋯ + f (n − 1)`. -/
def sumTo (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_eq (f : ℕ → ℤ) (n : ℕ) : sumTo f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumTo, ih, Finset.sum_range_succ]

/-- Whether `p i` for every `i < n`, testing `i = 0` first. -/
def allTo (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allTo p n && p n

theorem allTo_iff (p : ℕ → Bool) (n : ℕ) : allTo p n = true ↔ ∀ i < n, p i = true := by
  induction n with
  | zero => simp [allTo]
  | succ n ih =>
    simp only [allTo, Bool.and_eq_true, ih]
    exact ⟨fun ⟨h, hn⟩ i hi => (Nat.lt_succ_iff_lt_or_eq.1 hi).elim (h i) (· ▸ hn),
      fun h => ⟨fun i hi => h i (by omega), h n (by omega)⟩⟩

/-- Whether `p x` for the `m` integers `lo, lo + 1, …`, testing `lo` first. -/
def allRange (p : ℤ → Bool) (lo : ℤ) : ℕ → Bool
  | 0 => true
  | m + 1 => p lo && allRange p (lo + 1) m

theorem allRange_iff (p : ℤ → Bool) (lo : ℤ) (m : ℕ) :
    allRange p lo m = true ↔ ∀ x, lo ≤ x → x < lo + m → p x = true := by
  induction m generalizing lo with
  | zero =>
    simp only [allRange, true_iff, CharP.cast_eq_zero, add_zero]
    intro x h1 h2
    omega
  | succ m ih =>
    simp only [allRange, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h⟩ x h1 h2
      rcases eq_or_lt_of_le h1 with rfl | h1
      · exact h0
      · exact h x (by omega) (by push_cast at h2 ⊢; omega)
    · intro h
      exact ⟨h lo le_rfl (by omega), fun x h1 h2 => h x (by omega) (by push_cast at h2 ⊢; omega)⟩

/-- `allRange` over `[−b, b]`. -/
theorem allRange_abs {p : ℤ → Bool} {b : ℤ} (h : allRange p (-b) (2 * b + 1).toNat = true)
    {x : ℤ} (hx : |x| ≤ b) : p x = true := by
  rw [allRange_iff] at h
  have := abs_le.1 hx
  exact h x (by omega) (by rw [Int.toNat_of_nonneg (by omega)]; omega)

end SignedDifferenceSets
