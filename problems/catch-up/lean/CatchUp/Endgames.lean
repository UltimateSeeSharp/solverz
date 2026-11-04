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
  rw [margin, dite_eq_right Finset.not_nonempty_empty]

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
  · rw [margin, dite_eq_left (Finset.singleton_nonempty x)]
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
      split_ifs <;> omega
    · rw [Finset.mem_singleton.mp hy', hv]
      simp only [margin_singleton]
      split_ifs <;> omega
  apply le_antisymm
  · rw [margin, dite_eq_left (Finset.insert_nonempty u {v})]
    exact Finset.sup'_le _ _ fun y _ => opt y.1 y.2
  · by_cases hg : g ≤ u
    · have h := le_margin_of_mem (R := ({u, v} : Finset ℕ)) (x := v) (by simp) s (s + g)
      rw [hv, ite_eq_left (show s + g ≤ s + v by omega), margin_singleton] at h
      rw [ite_eq_left hg]
      push_cast at h
      linarith
    · have h := le_margin_of_mem (Finset.mem_insert_self u {v}) s (s + g)
      rw [hu, ite_eq_right (show ¬(s + g ≤ s + u) by omega), margin_singleton] at h
      rw [ite_eq_right hg]
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

/-- An adjacent pair `{u, u + 1}` with the mover trailing by 1 has margin 0 (C7: `g + u = v`). -/
theorem margin_adjacent_one {u : ℕ} (hu : 1 ≤ u) (s : ℕ) : margin {u, u + 1} s (s + 1) = 0 := by
  rw [margin_pair (by omega : u < u + 1), ite_eq_left hu]
  push_cast
  ring

/-- **C11** in margins: two adjacent pairs `{a, a + 1}`, `{b, b + 1}` with `1 ≤ a` and `a + 2 ≤ b`
have margin 0 at a tie. Every opening meets its partner, leaving the other pair at deficit 1,
worth 0; the opening `a + 1` leaves the opponent at most 0 whatever it answers. -/
theorem margin_two_pairs {a b : ℕ} (ha : 1 ≤ a) (hab : a + 2 ≤ b) (s : ℕ) :
    margin {a, a + 1, b, b + 1} s s = 0 := by
  obtain ⟨g, rfl⟩ : ∃ g, b = a + 2 + g := ⟨b - (a + 2), by omega⟩
  have hne : ({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).Nonempty :=
    Finset.insert_nonempty _ _
  -- The sets after one or two picks.
  have e1 : (({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase a).erase (a + 1) =
      {a + 2 + g, a + 2 + g + 1} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro h <;> omega
  have e2 : (({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 1)).erase a =
      {a + 2 + g, a + 2 + g + 1} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro h <;> omega
  have e3 : (({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 2 + g)).erase
      (a + 2 + g + 1) = {a, a + 1} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro h <;> omega
  have e4 : (({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 2 + g + 1)).erase
      (a + 2 + g) = {a, a + 1} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro h <;> omega
  have eT : ({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 1) =
      {a, a + 2 + g, a + 2 + g + 1} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro h <;> omega
  have t1 : ({a, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase a = {a + 2 + g, a + 2 + g + 1} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro h <;> omega
  have t2 : ({a, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 2 + g) = {a, a + 2 + g + 1} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro h <;> omega
  have t3 : ({a, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 2 + g + 1) = {a, a + 2 + g} := by
    ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor <;> intro h <;> omega
  have hb1 : 1 ≤ a + 2 + g := by omega
  -- Upper bound: after each opening the partner answer leaves the other pair at deficit 1.
  have hA1 : 0 ≤ margin (({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase a) s (s + a) := by
    have h := le_margin_of_mem
      (R := ({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase a) (x := a + 1) (by simp) s
      (s + a)
    rw [ite_eq_left (show s + a ≤ s + (a + 1) by omega), e1, show s + (a + 1) = s + a + 1 by ring,
      margin_adjacent_one hb1] at h
    linarith
  have hA2 : 0 ≤ margin (({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 1)) s
      (s + (a + 1)) := by
    have h := le_margin_of_mem
      (R := ({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 1)) (x := a) (by simp) s
      (s + (a + 1))
    rw [ite_eq_right (show ¬(s + (a + 1) ≤ s + a) by omega), e2,
      show s + (a + 1) = s + a + 1 by ring, margin_adjacent_one hb1] at h
    exact h
  have hA3 : 0 ≤ margin (({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 2 + g)) s
      (s + (a + 2 + g)) := by
    have h := le_margin_of_mem
      (R := ({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 2 + g))
      (x := a + 2 + g + 1)
      (by simp) s (s + (a + 2 + g))
    rw [ite_eq_left (show s + (a + 2 + g) ≤ s + (a + 2 + g + 1) by omega), e3,
      show s + (a + 2 + g + 1) = s + (a + 2 + g) + 1 by ring, margin_adjacent_one ha] at h
    linarith
  have hA4 : 0 ≤ margin (({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 2 + g + 1)) s
      (s + (a + 2 + g + 1)) := by
    have h := le_margin_of_mem
      (R := ({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 2 + g + 1))
      (x := a + 2 + g)
      (by simp) s (s + (a + 2 + g + 1))
    rw [ite_eq_right (show ¬(s + (a + 2 + g + 1) ≤ s + (a + 2 + g)) by omega), e4,
      show s + (a + 2 + g + 1) = s + (a + 2 + g) + 1 by ring, margin_adjacent_one ha] at h
    exact h
  -- Lower bound: after the opening a + 1 every answer leaves the opener at least 0.
  have hLow : margin (({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ).erase (a + 1)) s
      (s + (a + 1)) ≤ 0 := by
    rw [eT, margin, dite_eq_left (Finset.insert_nonempty _ _)]
    refine Finset.sup'_le _ _ fun y _ => ?_
    obtain ⟨y, hy⟩ := y
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    dsimp only
    rcases hy with h | h | h <;> subst y
    · rw [ite_eq_right (show ¬(s + (a + 1) ≤ s + a) by omega), t1,
        show s + (a + 1) = s + a + 1 by ring]
      exact (margin_adjacent_one hb1 (s + a)).le
    · rw [ite_eq_left (show s + (a + 1) ≤ s + (a + 2 + g) by omega), t2,
        show s + (a + 2 + g) = s + (a + 1) + (g + 1) by ring,
        margin_pair (show a < a + 2 + g + 1 by omega)]
      split_ifs <;> omega
    · rw [ite_eq_left (show s + (a + 1) ≤ s + (a + 2 + g + 1) by omega), t3,
        show s + (a + 2 + g + 1) = s + (a + 1) + (g + 2) by ring,
        margin_pair (show a < a + 2 + g by omega)]
      split_ifs <;> omega
  apply le_antisymm
  · rw [margin, dite_eq_left hne]
    refine Finset.sup'_le _ _ fun y _ => ?_
    obtain ⟨y, hy⟩ := y
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    dsimp only
    rw [ite_eq_left (Nat.le_add_right s y)]
    rcases hy with rfl | rfl | rfl | rfl <;> linarith [hA1, hA2, hA3, hA4]
  · have h := le_margin_of_mem (R := ({a, a + 1, a + 2 + g, a + 2 + g + 1} : Finset ℕ))
      (x := a + 1) (by simp) s s
    rw [ite_eq_left (Nat.le_add_right s (a + 1))] at h
    linarith

/-- **C11**: two adjacent pairs `{a, a + 1}`, `{b, b + 1}`, `1 ≤ a`, `a + 2 ≤ b`, draw at a tie. -/
theorem valueAux_two_pairs {a b : ℕ} (ha : 1 ≤ a) (hab : a + 2 ≤ b) (s : ℕ) :
    valueAux {a, a + 1, b, b + 1} s s false = .draw := by
  rw [valueAux_eq_ofMargin', margin_two_pairs ha hab]
  simp [Outcome.ofMargin]

/-- C11 for the game itself (opening flag). -/
theorem value_two_pairs {a b : ℕ} (ha : 1 ≤ a) (hab : a + 2 ≤ b) :
    value {a, a + 1, b, b + 1} = .draw := by
  rw [value, valueAux_true_eq_false, valueAux_two_pairs ha hab]

end CatchUp
