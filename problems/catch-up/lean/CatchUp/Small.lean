module

public import CatchUp.Executable
public import CatchUp.Token

/-!
# The conjecture for N ≤ 12

C1 for every `N ≤ 12` with an even total (`N = 0, 3, 4, 7, 8, 11, 12`), by the verified evaluator
(`eval_initial_eq_value` and `decide +kernel`): E1's values in this range, checked by the kernel.
-/

@[expose] public section

namespace CatchUp

/-- **C1 for `N ≤ 12`**. -/
theorem conjecture_le_twelve (N : ℕ) (hN12 : N ≤ 12) (hN : Even (N * (N + 1) / 2)) :
    value (Finset.Icc 1 N) = .draw := by
  rcases (even_triangle_iff N).1 hN with h | h
  · rcases (by omega : N = 0 ∨ N = 4 ∨ N = 8 ∨ N = 12) with rfl | rfl | rfl | rfl
    · exact value_Icc_zero
    · rw [← eval_initial_eq_value]
      decide +kernel
    · rw [← eval_initial_eq_value]
      decide +kernel
    · rw [← eval_initial_eq_value]
      decide +kernel
  · rcases (by omega : N = 3 ∨ N = 7 ∨ N = 11) with rfl | rfl | rfl
    · rw [← eval_initial_eq_value]
      decide +kernel
    · rw [← eval_initial_eq_value]
      decide +kernel
    · rw [← eval_initial_eq_value]
      decide +kernel

end CatchUp
