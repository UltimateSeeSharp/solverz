module

public import CatchUp.Linear
public import CatchUp.Parity

/-!
# Tests for `block_draw_linear`

Statement audit (`audit-statement`): the set is the block `{a..a+2p-1}`; for `p` even the
statement is Catch-Up itself on the block (`value`); the debt `p mod 2` cannot be dropped (parity);
`p = 0` holds trivially; it implies `block_draw_high` for `p ≥ 3`.
-/

@[expose] public section

namespace CatchUp

theorem map_range_eq_Icc {a n : ℕ} (hn : 1 ≤ n) :
    (Finset.range n).map (addLeftEmbedding a) = Finset.Icc a (a + n - 1) := by
  ext x
  simp only [Finset.mem_map, Finset.mem_range, addLeftEmbedding_apply, Finset.mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨x - a, by omega, by omega⟩

example : (Finset.range 4).map (addLeftEmbedding 10) = {10, 11, 12, 13} := by decide

/-- At equal scores a non-opening turn is one pick, like the opening. -/
theorem valueAux_true_eq_false (R : Finset ℕ) (s : ℕ) :
    valueAux R s s true = valueAux R s s false := by
  rw [valueAux, valueAux]
  simp only [↓reduceIte, Bool.false_eq_true, ge_iff_le, Nat.le_add_right]

/-- For `p` even it is Catch-Up itself on the block, player 1 opening. -/
theorem value_block_draw {p a : ℕ} (hp : 1 ≤ p) (hpe : Even p) (ha : 3 * (2 * p - 1) < a) :
    value (Finset.Icc a (a + 2 * p - 1)) = .draw := by
  rw [value, ← map_range_eq_Icc (by omega), valueAux_true_eq_false]
  have := block_draw_linear hp ha 0
  rwa [Nat.even_iff.mp hpe, Nat.add_zero] at this

example : value (Finset.Icc 10 13) = .draw := value_block_draw (p := 2) (by norm_num) (by decide)
  (by norm_num)

theorem sum_block (p a : ℕ) :
    ∑ x ∈ (Finset.range (2 * p)).map (addLeftEmbedding a), x = 2 * p * a + p * (2 * p - 1) := by
  rw [Finset.sum_map]
  simp only [addLeftEmbedding_apply]
  rw [Finset.sum_add_distrib, sum_range_two_mul, Finset.sum_const, Finset.card_range]
  simp

/-- Dropping the debt: at a debt of the other parity the block is never a draw. -/
theorem block_not_draw_of_parity {p a s d : ℕ} (hd : d % 2 ≠ p % 2) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + d) false ≠ .draw := by
  intro h
  have := parity_law _ _ _ _ h
  rw [sum_block, Nat.even_iff] at this
  have h2 : p * (2 * p - 1) % 2 = p % 2 := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; rfl
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have e1 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
      have e2 : (q + 1) * (2 * q + 1) = 2 * (q * q + q) + (q + 1) := by ring
      rw [e1]
      omega
  have h3 : 2 * p * a % 2 = 0 := by rw [Nat.mul_assoc]; exact Nat.mul_mod_right 2 _
  omega

/-- Dropping `1 ≤ p`: the empty block is a draw anyway. -/
example (a s : ℕ) :
    valueAux ((Finset.range (2 * 0)).map (addLeftEmbedding a)) s (s + 0 % 2) false = .draw := by
  rw [valueAux]
  simp

/-- It implies `block_draw_high` for `p ≥ 3` (the heights there are larger). -/
example {p a : ℕ} (hp : 3 ≤ p) (ha : p % 2 + p * (2 * p - 1) < a) (s : ℕ) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + p % 2) false = .draw :=
  block_draw_linear (by omega) (lt_of_le_of_lt (le_trans (Nat.mul_le_mul_right _ hp)
    (Nat.le_add_left _ _)) ha) s

end CatchUp
