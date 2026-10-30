module

public import CatchUp.Hyb2
public import CatchUp.Tests.BlockDrawLinear

/-!
# Tests for `block_draw_hyb2`

Statement audit (`audit`): the same statement as `block_draw_linear` with the height
lowered to `a ≥ 2p − 1`; for `p` even it is Catch-Up itself on the block; it implies
`block_draw_linear` and `block_draw_high`; the smallest block it covers at `p = 2` is
`{3, 4, 5, 6}`.
-/

@[expose] public section

namespace CatchUp

/-- For `p` even it is Catch-Up itself on the block, player 1 opening. -/
theorem value_block_draw_hyb2 {p a : ℕ} (hp : 1 ≤ p) (hpe : Even p) (ha : 2 * p - 1 ≤ a) :
    value (Finset.Icc a (a + 2 * p - 1)) = .draw := by
  rw [value, ← map_range_eq_Icc (by omega), valueAux_true_eq_false]
  have := block_draw_hyb2 hp ha 0
  rwa [Nat.even_iff.mp hpe, Nat.add_zero] at this

example : value (Finset.Icc 3 6) = .draw :=
  value_block_draw_hyb2 (p := 2) (by norm_num) (by decide) (by norm_num)

/-- It implies `block_draw_linear` (the height there is larger). -/
example {p a : ℕ} (hp : 1 ≤ p) (ha : 3 * (2 * p - 1) < a) (s : ℕ) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + p % 2) false = .draw :=
  block_draw_hyb2 hp (by omega) s

/-- It implies `block_draw_high` for every `p ≥ 1`. -/
example {p a : ℕ} (hp : 1 ≤ p) (ha : p % 2 + p * (2 * p - 1) < a) (s : ℕ) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + p % 2) false = .draw := by
  have h : 2 * p - 1 ≤ p * (2 * p - 1) := Nat.le_mul_of_pos_left _ hp
  exact block_draw_hyb2 hp (by omega) s

end CatchUp
