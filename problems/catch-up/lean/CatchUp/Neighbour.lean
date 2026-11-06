module

public import CatchUp.GameMargin

/-!
# Neighbour bound

C107 in margins: when the mover trailing by `d = b - a` ends its turn with the single pick `x`, the
opponent may answer with a neighbour of `x`, which always catches up (`x + 1` always, `x - 1` when
`d ≥ 1`). So the pick is worth at most the margin of the mover after that answer, trailing by
`d + 1` or `d - 1` on the set without both numbers.
-/

@[expose] public section

namespace CatchUp

/-- **Neighbour bound, upper neighbour** (C107 (i)): the pick `x` is worth at most the mover's
margin after the answer `x + 1`, trailing by one more. -/
theorem neg_margin_erase_le_of_succ {S : Finset ℕ} {x a b : ℕ} (hx1 : x + 1 ∈ S) (hab : a ≤ b) :
    -margin (S.erase x) b (a + x) ≤ margin ((S.erase x).erase (x + 1)) (a + x) (b + (x + 1)) := by
  have hy : x + 1 ∈ S.erase x := Finset.mem_erase.mpr ⟨by omega, hx1⟩
  have h := le_margin_of_mem hy b (a + x)
  rw [ite_eq_left (show a + x ≤ b + (x + 1) by omega)] at h
  linarith

/-- **Neighbour bound, lower neighbour** (C107 (ii)): for a mover strictly behind, the pick `x`
is worth at most the mover's margin after the answer `x - 1`, trailing by one less. -/
theorem neg_margin_erase_le_of_pred {S : Finset ℕ} {x a b : ℕ} (hx1 : x - 1 ∈ S) (hx : 1 ≤ x)
    (hab : a < b) :
    -margin (S.erase x) b (a + x) ≤ margin ((S.erase x).erase (x - 1)) (a + x) (b + (x - 1)) := by
  have hy : x - 1 ∈ S.erase x := Finset.mem_erase.mpr ⟨by omega, hx1⟩
  have h := le_margin_of_mem hy b (a + x)
  rw [ite_eq_left (show a + x ≤ b + (x - 1) by omega)] at h
  linarith

end CatchUp
