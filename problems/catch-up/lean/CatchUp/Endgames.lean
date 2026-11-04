module

public import CatchUp.GameMargin

/-!
# Endgames with at most two numbers

Claim C7, through the sign lemma (C33): the margin of `{x}` is `a + x - b` whoever ends ahead,
and of `{u, v}` with `u < v`, the mover trailing by `g`, it is `v - u - g` if `g ≤ u` (the mover
takes `v`) and `u + v - g` otherwise (it takes both). The values are their signs
(`valueAux_empty_gap`, `valueAux_singleton_gap`, `valueAux_pair_gap`).
-/

@[expose] public section

namespace CatchUp

theorem margin_empty (a b : ℕ) : margin ∅ a b = (a : ℤ) - b := by
  rw [margin, dif_neg Finset.not_nonempty_empty]

/-- One number left: the mover's margin is `a + x - b`, whether or not it catches up. -/
theorem margin_singleton (x a b : ℕ) : margin {x} a b = (a : ℤ) + x - b := by
  have key : ∀ y ∈ ({x} : Finset ℕ),
      (if b ≤ a + y then -margin (({x} : Finset ℕ).erase y) b (a + y)
        else margin (({x} : Finset ℕ).erase y) (a + y) b) = (a : ℤ) + x - b := by
    intro y hy
    rw [Finset.mem_singleton.mp hy, Finset.erase_singleton]
    simp only [margin_empty]
    split_ifs <;> (push_cast; ring)
  apply le_antisymm
  · rw [margin, dif_pos (Finset.singleton_nonempty x)]
    exact Finset.sup'_le _ _ fun y _ => (key y.1 y.2).le
  · have h := le_margin_of_mem (Finset.mem_singleton_self x) a b
    rwa [key x (Finset.mem_singleton_self x)] at h

/-- Two numbers `u < v`, the mover trailing by `g`: `v - u - g` if `g ≤ u`, else `u + v - g`. -/
theorem margin_pair {u v : ℕ} (huv : u < v) (s g : ℕ) :
    margin {u, v} s (s + g) = if g ≤ u then (v : ℤ) - u - g else (u : ℤ) + v - g := by
  have hu : ({u, v} : Finset ℕ).erase u = {v} := Finset.erase_insert (by simp [huv.ne])
  have hv : ({u, v} : Finset ℕ).erase v = {u} := by
    rw [Finset.erase_insert_of_ne huv.ne, Finset.erase_singleton, Finset.insert_empty]
  have opt : ∀ y ∈ ({u, v} : Finset ℕ),
      (if s + g ≤ s + y then -margin (({u, v} : Finset ℕ).erase y) (s + g) (s + y)
        else margin (({u, v} : Finset ℕ).erase y) (s + y) (s + g)) ≤
        (if g ≤ u then (v : ℤ) - u - g else (u : ℤ) + v - g) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · rw [hu]
      simp only [margin_singleton]
      split_ifs <;> (try push_cast) <;> omega
    · rw [Finset.mem_singleton.mp hy', hv]
      simp only [margin_singleton]
      split_ifs <;> (try push_cast) <;> omega
  apply le_antisymm
  · rw [margin, dif_pos (Finset.insert_nonempty u {v})]
    exact Finset.sup'_le _ _ fun y _ => opt y.1 y.2
  · by_cases hg : g ≤ u
    · have h := le_margin_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
        s (s + g)
      rw [hv, if_pos (show s + g ≤ s + v by omega), margin_singleton] at h
      rw [if_pos hg]
      push_cast at h
      linarith
    · have h := le_margin_of_mem (Finset.mem_insert_self u {v}) s (s + g)
      rw [hu, if_neg (show ¬(s + g ≤ s + u) by omega), margin_singleton] at h
      rw [if_neg hg]
      push_cast at h
      linarith

/-- C7, no number left: a draw exactly at a tie. -/
theorem valueAux_empty_gap (s g : ℕ) :
    valueAux ∅ s (s + g) false = if g = 0 then .draw else .loss := by
  rw [valueAux_eq_ofMargin', margin_empty]
  unfold Outcome.ofMargin
  split_ifs <;> first | rfl | (exfalso; omega)

/-- C7, one number `x`: a win if the mover trails by less than `x`, a draw at exactly `x`. -/
theorem valueAux_singleton_gap (x s g : ℕ) :
    valueAux {x} s (s + g) false = if g < x then .win else if g = x then .draw else .loss := by
  rw [valueAux_eq_ofMargin', margin_singleton]
  unfold Outcome.ofMargin
  split_ifs <;> first | rfl | (exfalso; omega)

/-- C7, two numbers `u < v`, the mover trailing by `g`. -/
theorem valueAux_pair_gap {u v : ℕ} (huv : u < v) (s g : ℕ) :
    valueAux {u, v} s (s + g) false =
      if g ≤ u then (if g + u < v then .win else if g + u = v then .draw else .loss)
      else (if g < u + v then .win else if g = u + v then .draw else .loss) := by
  rw [valueAux_eq_ofMargin', margin_pair huv]
  unfold Outcome.ofMargin
  split_ifs <;> first | rfl | (exfalso; omega)

end CatchUp
