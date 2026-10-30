module

public import CatchUp.Matching
public import CatchUp.Margin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The matching cost as a parity count

For an even set `O` of naturals at most `M`, C20's bottom-up matching cost is the number of points
`x < M` at which an odd number of elements of `O` are `≤ x` (`matchCost_eq_card_odd`): the matched
gaps `[o₁, o₂), [o₃, o₄), …` are exactly those points. Removing two elements `i < j` flips that
parity on `[i, j)` and nowhere else, so the cost changes by `(j - i) - 2 O(i, j)`, with `O(i, j)`
the odd points in `[i, j)` (`matchCost_erase_two`). Used by the potential W of C24.
-/

@[expose] public section

namespace CatchUp

/-- Whether an odd number of elements of `O` are at most `x`. -/
def OddBelow (O : Finset ℕ) (x : ℕ) : Prop := Odd (O.filter (· ≤ x)).card

instance (O : Finset ℕ) (x : ℕ) : Decidable (OddBelow O x) := by
  unfold OddBelow; infer_instance

theorem card_filter_le_erase {O : Finset ℕ} {i : ℕ} (hi : i ∈ O) (x : ℕ) :
    ((O.erase i).filter (· ≤ x)).card + (if i ≤ x then 1 else 0) = (O.filter (· ≤ x)).card := by
  rw [Finset.filter_erase]
  split_ifs with h
  · exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hi, h⟩)
  · rw [Finset.erase_eq_of_notMem (by simp [h])]
    rfl

theorem oddBelow_erase_two {O : Finset ℕ} {i j : ℕ} (hi : i ∈ O) (hj : j ∈ O.erase i) (hij : i < j)
    (x : ℕ) : OddBelow ((O.erase i).erase j) x ↔ (OddBelow O x ↔ ¬ (i ≤ x ∧ x < j)) := by
  have h1 := card_filter_le_erase hi x
  have h2 := card_filter_le_erase hj x
  unfold OddBelow
  rw [Nat.odd_iff, Nat.odd_iff]
  split_ifs at h1 h2 <;> omega

/-- **The parity form of C20's cost.** -/
theorem matchCost_eq_card_odd (n : ℕ) : ∀ O : Finset ℕ, O.card = n → Even n → ∀ M : ℕ,
    (∀ o ∈ O, o ≤ M) → matchCost O = ((Finset.range M).filter (OddBelow O)).card := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro O hn hev M hM
  subst hn
  by_cases h : O.Nonempty
  · obtain ⟨a, ha, hamin⟩ : ∃ a ∈ O, ∀ x ∈ O, a ≤ x :=
      ⟨O.min' h, Finset.min'_mem O h, fun x hx => Finset.min'_le O x hx⟩
    have h' := erase_nonempty_of_even hev ha
    obtain ⟨b, hbE, hbmin⟩ : ∃ b ∈ O.erase a, ∀ x ∈ O.erase a, b ≤ x :=
      ⟨(O.erase a).min' h', Finset.min'_mem _ h', fun x hx => Finset.min'_le _ x hx⟩
    have hb := Finset.mem_of_mem_erase hbE
    have hab : a < b := lt_of_le_of_ne (hamin b hb) (Finset.mem_erase.mp hbE).1.symm
    have hmin : ∀ x ∈ O, x = a ∨ b ≤ x := by
      intro x hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr (hbmin x (Finset.mem_erase.mpr ⟨hxa, hx⟩))
    rw [matchCost_of_min ha hb hab hmin]
    have hc1 := Finset.card_erase_add_one ha
    have hc2 := Finset.card_erase_add_one hbE
    obtain ⟨k, hk⟩ := hev
    have hIH := ih _ (by omega) ((O.erase a).erase b) rfl ⟨k - 1, by omega⟩ M
      (fun o ho => hM o (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ho)))
    rw [hIH]
    -- The odd points of `O` are `[a, b)` and those of the rest, which all lie at or above `b`.
    have hrest : ∀ x < b, ((((O.erase a).erase b)).filter (· ≤ x)).card = 0 := by
      intro x hx
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y hy
      have hy1 := Finset.mem_erase.mp hy
      have hy2 := Finset.mem_erase.mp hy1.2
      rcases hmin y hy2.2 with h1 | h1
      · exact absurd h1 hy2.1
      · omega
    have hsplit : (Finset.range M).filter (OddBelow O) =
        (Finset.range M).filter (fun x => a ≤ x ∧ x < b) ∪
          (Finset.range M).filter (OddBelow ((O.erase a).erase b)) := by
      rw [← Finset.filter_or]
      apply Finset.filter_congr
      intro x _
      have h1 := card_filter_le_erase ha x
      have h2 := card_filter_le_erase hbE x
      unfold OddBelow
      rw [Nat.odd_iff, Nat.odd_iff]
      by_cases hxb : x < b
      · have := hrest x hxb
        split_ifs at h1 h2 <;> omega
      · split_ifs at h1 h2 <;> omega
    have hdisj : Disjoint ((Finset.range M).filter (fun x => a ≤ x ∧ x < b))
        ((Finset.range M).filter (OddBelow ((O.erase a).erase b))) := by
      rw [Finset.disjoint_filter]
      intro x _ hx hodd
      unfold OddBelow at hodd
      rw [hrest x hx.2] at hodd
      exact Nat.not_odd_zero hodd
    have hIco : (Finset.range M).filter (fun x => a ≤ x ∧ x < b) = Finset.Ico a b := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      have := hM b hb
      omega
    rw [hsplit, Finset.card_union_of_disjoint hdisj, hIco, Nat.card_Ico]
    push_cast [hab.le]
    ring
  · have h0 : O = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst h0
    rw [matchCost_empty, Finset.filter_false_of_mem (fun x _ => ?_)]
    · simp
    · unfold OddBelow
      simp

/-- **Removing two numbers** `i < j` changes the cost by `(j - i)` minus twice the odd points
in `[i, j)`. -/
theorem matchCost_erase_two {O : Finset ℕ} (hev : Even O.card) {i j M : ℕ} (hi : i ∈ O)
    (hj : j ∈ O.erase i) (hij : i < j) (hM : ∀ o ∈ O, o ≤ M) :
    matchCost ((O.erase i).erase j) + 2 * (((Finset.Ico i j).filter (OddBelow O)).card : ℤ) =
      matchCost O + (j - i) := by
  have hc1 := Finset.card_erase_add_one hi
  have hc2 := Finset.card_erase_add_one hj
  obtain ⟨k, hk⟩ := hev
  have hjM := hM j (Finset.mem_of_mem_erase hj)
  rw [matchCost_eq_card_odd _ O rfl ⟨k, hk⟩ M hM,
    matchCost_eq_card_odd _ ((O.erase i).erase j) rfl ⟨k - 1, by omega⟩ M
      (fun o ho => hM o (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ho)))]
  have hI : (Finset.Ico i j).filter (OddBelow O) =
      (Finset.range M).filter (fun x => (i ≤ x ∧ x < j) ∧ OddBelow O x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  have hJ : (j : ℤ) - i = ((Finset.range M).filter (fun x => i ≤ x ∧ x < j)).card := by
    have : (Finset.range M).filter (fun x => i ≤ x ∧ x < j) = Finset.Ico i j := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [this, Nat.card_Ico]
    push_cast [hij.le]
    ring
  rw [hI, hJ]
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have := oddBelow_erase_two hi hj hij x
  by_cases hx : i ≤ x ∧ x < j <;> by_cases hp : OddBelow O x
  · have hn : ¬ OddBelow ((O.erase i).erase j) x := by tauto
    simp [hx, hp, hn]
  · have hn : OddBelow ((O.erase i).erase j) x := by tauto
    simp [hx, hp, hn]
  · have hn : OddBelow ((O.erase i).erase j) x := by tauto
    simp [hx, hp, hn]
  · have hn : ¬ OddBelow ((O.erase i).erase j) x := by tauto
    simp [hx, hp, hn]

end CatchUp
