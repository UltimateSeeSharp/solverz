module

public import CatchUp.Hyb2
public import CatchUp.Executable

/-!
# The draw band of blocks at every height, small blocks

Claim C86 for `p ≤ 3`: the block `{a..a+2p-1}` with the mover trailing by any `d ≤ p` of the
parity of `p` is a draw at every height `a ≥ 1`, except `{2, 3, 4, 5}` at deficit 2, a mover win
(`band_exception`). From `a ≥ 2p - 1` it is `block_row_draw_hyb2` (C24); below, the ten remaining
positions are evaluated by the verified evaluator (`band_draw_le_three`).
-/

@[expose] public section

namespace CatchUp

/-- Any ordinary-turn position is the verified evaluator's normalized position. -/
theorem valueAux_eq_eval (R : Finset ℕ) (s d : ℕ) :
    valueAux R s (s + d) false = Position.eval ⟨R, d⟩ := by
  rw [← Position.eval_eq_value_aux R s (s + d) (by omega), Nat.add_sub_cancel_left]

/-- C47's exception: `{2, 3, 4, 5}` at deficit 2 is a mover win. -/
theorem band_exception (s : ℕ) :
    valueAux ((Finset.range (2 * 2)).map (addLeftEmbedding 2)) s (s + 2) false = .win := by
  rw [valueAux_eq_eval]
  decide +kernel

/-- **C86 for `p ≤ 3`**: blocks draw on the whole band at every height, but for `(2, 2, 2)`. -/
theorem band_draw_le_three {p a d : ℕ} (hp1 : 1 ≤ p) (hp3 : p ≤ 3) (ha : 1 ≤ a) (hd : d ≤ p)
    (hdp : d % 2 = p % 2) (hex : ¬(p = 2 ∧ a = 2 ∧ d = 2)) (s : ℕ) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + d) false = .draw := by
  by_cases hhigh : 2 * p - 1 ≤ a
  · exact block_row_draw_hyb2 hp1 hhigh hd hdp s
  · rw [valueAux_eq_eval]
    have hcases : (p = 2 ∧ a = 1 ∧ (d = 0 ∨ d = 2)) ∨ (p = 2 ∧ a = 2 ∧ d = 0) ∨
        (p = 3 ∧ (a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) ∧ (d = 1 ∨ d = 3)) := by omega
    rcases hcases with ⟨rfl, rfl, rfl | rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl | rfl | rfl | rfl, rfl | rfl⟩ <;> decide +kernel

end CatchUp
