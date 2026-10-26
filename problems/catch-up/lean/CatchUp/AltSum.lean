module

public import CatchUp.Statement
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Top-down alternating sums and the greedy bound

Blueprint L14. `altSum T = t₁ - t₂ + t₃ - ⋯` for `T` sorted decreasingly. One round in which
Z takes the largest number `t₁` and the opponent any other `j` changes `altSum` by at most
`t₁ - j` either way (`altSum_round`); if the opponent takes `t₁` and Z the next largest `t₂`, it
drops by exactly `t₁ - t₂` (`altSum_top_two`). Hence a player who always takes the largest number
loses by at most `altSum T`, whoever picks first in each round (`neg_altSum_le_greedyWorst`).
-/

public section

namespace CatchUp

/-- Top-down alternating sum `t₁ - t₂ + t₃ - ⋯` of a finite set sorted decreasingly. -/
noncomputable def altSum (T : Finset ℕ) : ℤ :=
  if h : T.Nonempty then (T.max' h : ℤ) - altSum (T.erase (T.max' h)) else 0
termination_by T.card
decreasing_by exact Finset.card_erase_lt_of_mem (Finset.max'_mem T h)

theorem altSum_empty : altSum ∅ = 0 := by
  rw [altSum]; simp

theorem altSum_of_nonempty {T : Finset ℕ} (h : T.Nonempty) :
    altSum T = (T.max' h : ℤ) - altSum (T.erase (T.max' h)) := by
  rw [altSum]; simp only [h, ↓reduceDIte]

/-- Removing a number other than the maximum keeps the maximum. -/
private theorem max'_erase_of_ne {U : Finset ℕ} (hU : U.Nonempty) {x : ℕ}
    (hx : x ≠ U.max' hU) (h' : (U.erase x).Nonempty) : (U.erase x).max' h' = U.max' hU := by
  apply le_antisymm
  · exact Finset.max'_le _ _ _ fun y hy => Finset.le_max' U y (Finset.mem_of_mem_erase hy)
  · exact Finset.le_max' _ _ (Finset.mem_erase.mpr ⟨Ne.symm hx, Finset.max'_mem U hU⟩)

/-- The joint bound: for `x ∈ U`, `x ≤ altSum U + altSum (U \ {x}) ≤ 2 max U - x`, with equality
on the left when `x` is the maximum. -/
theorem altSum_add_erase (n : ℕ) : ∀ (U : Finset ℕ), U.card = n → ∀ (hU : U.Nonempty) x, x ∈ U →
    (x : ℤ) ≤ altSum U + altSum (U.erase x) ∧
      altSum U + altSum (U.erase x) ≤ 2 * (U.max' hU : ℤ) - x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn hU x hx
  rw [altSum_of_nonempty hU]
  by_cases hxm : x = U.max' hU
  · subst hxm
    constructor <;> linarith
  · have hxV : x ∈ U.erase (U.max' hU) := Finset.mem_erase.mpr ⟨hxm, hx⟩
    have hV : (U.erase (U.max' hU)).Nonempty := ⟨x, hxV⟩
    have h' : (U.erase x).Nonempty := ⟨U.max' hU, Finset.mem_erase.mpr ⟨Ne.symm hxm,
      Finset.max'_mem U hU⟩⟩
    rw [altSum_of_nonempty h', max'_erase_of_ne hU hxm h', Finset.erase_right_comm]
    have hlt : (U.erase (U.max' hU)).card < n := hn ▸ Finset.card_erase_lt_of_mem
      (Finset.max'_mem U hU)
    obtain ⟨h1, h2⟩ := ih _ hlt _ rfl hV x hxV
    have hmV : (U.erase (U.max' hU)).max' hV ≤ U.max' hU :=
      Finset.max'_le _ _ _ fun y hy => Finset.le_max' U y (Finset.mem_of_mem_erase hy)
    have hmV' : ((U.erase (U.max' hU)).max' hV : ℤ) ≤ U.max' hU := by exact_mod_cast hmV
    constructor <;> linarith

/-- One round where Z takes the largest number `t₁` and the opponent another number `j`: the
alternating sum changes by at most `t₁ - j` either way (L14's per-round inequality and L18 (a)). -/
theorem altSum_round {T : Finset ℕ} (h : T.Nonempty) {j : ℕ} (hj : j ∈ T.erase (T.max' h)) :
    |altSum T - altSum ((T.erase (T.max' h)).erase j)| ≤ (T.max' h : ℤ) - j := by
  have hU : (T.erase (T.max' h)).Nonempty := ⟨j, hj⟩
  obtain ⟨h1, h2⟩ := altSum_add_erase _ _ rfl hU j hj
  have hmU : (T.erase (T.max' h)).max' hU < T.max' h := by
    apply lt_of_le_of_ne
    · exact Finset.max'_le _ _ _ fun y hy => Finset.le_max' T y (Finset.mem_of_mem_erase hy)
    · exact fun he => (Finset.notMem_erase _ T) (he ▸ Finset.max'_mem _ hU)
  have hmU' : ((T.erase (T.max' h)).max' hU : ℤ) < T.max' h := by exact_mod_cast hmU
  rw [altSum_of_nonempty h, abs_le]
  constructor <;> linarith

/-- The opponent takes the largest number `t₁` and Z the next largest `t₂`: the alternating sum
drops by exactly `t₁ - t₂`. -/
theorem altSum_top_two {T : Finset ℕ} (h : T.Nonempty) (h' : (T.erase (T.max' h)).Nonempty) :
    altSum T - altSum ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' h')) =
      (T.max' h : ℤ) - (T.erase (T.max' h)).max' h' := by
  rw [altSum_of_nonempty h, altSum_of_nonempty h']
  ring

/-- Worst case, over the opponent's picks and the order of the two picks in each round, of Z's
total minus the opponent's when Z always takes the largest number left. A round: Z takes the
largest `t₁` and the opponent some `j` (in either order), or the opponent takes `t₁` first and Z
the next largest. With one number left (odd `T`), Z takes it. -/
noncomputable def greedyWorst (T : Finset ℕ) : ℤ :=
  if h : T.Nonempty then
    if h' : (T.erase (T.max' h)).Nonempty then
      min ((T.erase (T.max' h)).attach.inf' (by simpa using h') fun j =>
          (T.max' h : ℤ) - j + greedyWorst ((T.erase (T.max' h)).erase j))
        ((T.erase (T.max' h)).max' h' - T.max' h +
          greedyWorst ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' h')))
    else T.max' h
  else 0
termination_by T.card
decreasing_by
  · exact lt_trans (Finset.card_erase_lt_of_mem j.2)
      (Finset.card_erase_lt_of_mem (Finset.max'_mem T h))
  · exact lt_trans (Finset.card_erase_lt_of_mem (Finset.max'_mem _ h'))
      (Finset.card_erase_lt_of_mem (Finset.max'_mem T h))

/-- **L14 (greedy bound).** If Z always takes the largest number left, Z's total minus the
opponent's over an even set `T` is at least `-altSum T`, whatever the opponent picks and whoever
picks first in each round. -/
theorem neg_altSum_le_greedyWorst (n : ℕ) : ∀ (T : Finset ℕ), T.card = n → Even n →
    -altSum T ≤ greedyWorst T := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn hev
  rw [greedyWorst]
  by_cases h : T.Nonempty
  · simp only [h, ↓reduceDIte]
    have hcard1 : (T.erase (T.max' h)).card + 1 = T.card :=
      Finset.card_erase_add_one (Finset.max'_mem T h)
    by_cases h' : (T.erase (T.max' h)).Nonempty
    · simp only [h', ↓reduceDIte]
      have step : ∀ j ∈ T.erase (T.max' h),
          -altSum T ≤ (T.max' h : ℤ) - j + greedyWorst ((T.erase (T.max' h)).erase j) := by
        intro j hj
        have hcard2 : ((T.erase (T.max' h)).erase j).card + 1 = (T.erase (T.max' h)).card :=
          Finset.card_erase_add_one hj
        have hev2 : Even ((T.erase (T.max' h)).erase j).card := by
          obtain ⟨k, hk⟩ := hev
          exact ⟨k - 1, by omega⟩
        have hih := ih _ (by omega) _ rfl hev2
        have hr := abs_le.mp (altSum_round h hj)
        linarith [hr.1]
      apply le_min
      · apply Finset.le_inf'
        intro j _
        exact step j.1 j.2
      · have hj := Finset.max'_mem _ h'
        have hcard2 : ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' h')).card + 1 =
            (T.erase (T.max' h)).card := Finset.card_erase_add_one hj
        have hev2 : Even ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' h')).card := by
          obtain ⟨k, hk⟩ := hev
          exact ⟨k - 1, by omega⟩
        have hih := ih _ (by omega) _ rfl hev2
        have ht := altSum_top_two h h'
        linarith
    · -- One number left: impossible for even `T`.
      exfalso
      have h0 : T.erase (T.max' h) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h'
      rw [h0, Finset.card_empty] at hcard1
      obtain ⟨k, hk⟩ := hev
      omega
  · simp only [h, ↓reduceDIte]
    rw [Finset.not_nonempty_iff_eq_empty.mp h, altSum_empty]
    simp

end CatchUp
