module

public import CatchUp.Margin
public import CatchUp.Token
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Margins of Catch-Up

`margin R a b` is the minimax final margin of Catch-Up after the opening: `R` left, the mover
holding `a` and the opponent `b`, both players maximizing their own margin, and no early-loss
rule (a mover who cannot catch up keeps picking).
* C33, sign lemma on sets: the value is its sign (`valueAux_eq_ofMargin`); the early-loss rule
  agrees because the margin never exceeds `a + ∑ R - b` (`margin_bounds`).
* C38, two-token lemma: at a tie, the opponent's margins after two openings `y < t` sum to at
  least 0 (`margin_two_token`).
* C37 (3): the margin has the parity of `a + b + ∑ R` (`even_margin_add`), so a margin of at most
  1 in absolute value at `{1..N}` for every even total gives the conjecture
  (`conjecture_of_margin_le_one`).
-/

@[expose] public section

namespace CatchUp

/-- The minimax final margin (the mover's score minus the opponent's) of Catch-Up after the
opening, with `R` left and scores `a` (mover) and `b`; no early-loss rule. -/
noncomputable def margin (R : Finset ℕ) (a b : ℕ) : ℤ :=
  if h : R.Nonempty then
    R.attach.sup' (by simpa using h) fun x =>
      if b ≤ a + x.1 then -margin (R.erase x.1) b (a + x.1)
      else margin (R.erase x.1) (a + x.1) b
  else (a : ℤ) - b
termination_by R.card
decreasing_by
  all_goals exact Finset.card_erase_lt_of_mem x.2

/-- Every final margin lies between taking nothing and taking everything left. -/
theorem margin_bounds (n : ℕ) : ∀ (R : Finset ℕ), R.card = n → ∀ a b : ℕ,
    (a : ℤ) - b - ∑ x ∈ R, (x : ℤ) ≤ margin R a b ∧
      margin R a b ≤ (a : ℤ) + ∑ x ∈ R, (x : ℤ) - b := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hn a b
  subst hn
  by_cases h : R.Nonempty
  · rw [margin, dif_pos h]
    have key : ∀ x ∈ R,
        (a : ℤ) - b - ∑ y ∈ R, (y : ℤ) ≤
            (if b ≤ a + x then -margin (R.erase x) b (a + x)
              else margin (R.erase x) (a + x) b) ∧
          (if b ≤ a + x then -margin (R.erase x) b (a + x)
              else margin (R.erase x) (a + x) b) ≤ (a : ℤ) + ∑ y ∈ R, (y : ℤ) - b := by
      intro x hx
      have hlt : (R.erase x).card < R.card := Finset.card_erase_lt_of_mem hx
      have hs : ∑ y ∈ R.erase x, (y : ℤ) + x = ∑ y ∈ R, (y : ℤ) := Finset.sum_erase_add R _ hx
      have hx0 : (0 : ℤ) ≤ x := by positivity
      by_cases hc : b ≤ a + x
      · obtain ⟨h1, h2⟩ := ih _ hlt (R.erase x) rfl b (a + x)
        rw [if_pos hc]
        push_cast at h1 h2
        constructor <;> linarith
      · obtain ⟨h1, h2⟩ := ih _ hlt (R.erase x) rfl (a + x) b
        rw [if_neg hc]
        push_cast at h1 h2
        constructor <;> linarith
    constructor
    · obtain ⟨x, hx⟩ := id h
      apply Finset.le_sup'_of_le _ (Finset.mem_attach R ⟨x, hx⟩)
      exact (key x hx).1
    · exact Finset.sup'_le _ _ fun x _ => (key x.1 x.2).2
  · have h0 : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst h0
    rw [margin, dif_neg Finset.not_nonempty_empty]
    simp

/-- **Sign lemma** (C33): after the opening, Catch-Up's value is the sign of the minimax margin. -/
theorem valueAux_eq_ofMargin (n : ℕ) : ∀ (R : Finset ℕ), R.card = n → ∀ a b : ℕ,
    valueAux R a b false = Outcome.ofMargin (margin R a b) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hn a b
  subst hn
  by_cases h0 : R = ∅
  · subst h0
    rw [valueAux_empty, margin, dif_neg Finset.not_nonempty_empty]
    unfold Outcome.ofMargin
    split_ifs <;> first | rfl | (exfalso; omega)
  · have hne : R.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    by_cases hl : a + ∑ x ∈ R, x < b
    · rw [valueAux_early_loss hl]
      have hub := (margin_bounds _ R rfl a b).2
      have hl' : ((a + ∑ x ∈ R, x : ℕ) : ℤ) < (b : ℤ) := by exact_mod_cast hl
      push_cast at hl'
      have hm : margin R a b < 0 := by linarith
      simp [Outcome.ofMargin, hm, not_lt.mpr hm.le]
    · rw [valueAux_step h0 hl, margin, dif_pos hne]
      apply Outcome.best_eq_ofMargin_sup'
      intro o
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and]
      have key : ∀ x (hx : x ∈ R),
          (if a + x ≥ b then (valueAux (R.erase x) b (a + x) false).neg
            else valueAux (R.erase x) (a + x) b false) =
          Outcome.ofMargin (if b ≤ a + x then -margin (R.erase x) b (a + x)
            else margin (R.erase x) (a + x) b) := by
        intro x hx
        have hlt : (R.erase x).card < R.card := Finset.card_erase_lt_of_mem hx
        by_cases hc : b ≤ a + x
        · simp only [ge_iff_le, if_pos hc]
          rw [ih _ hlt (R.erase x) rfl, Outcome.ofMargin_neg]
        · simp only [ge_iff_le, if_neg hc]
          rw [ih _ hlt (R.erase x) rfl]
      constructor
      · rintro ⟨⟨x, hx⟩, rfl⟩
        exact ⟨⟨x, hx⟩, key x hx⟩
      · rintro ⟨⟨x, hx⟩, rfl⟩
        exact ⟨⟨x, hx⟩, key x hx⟩

/-- The sign lemma for every position after the opening, without the size argument. -/
theorem valueAux_eq_ofMargin' (R : Finset ℕ) (a b : ℕ) :
    valueAux R a b false = Outcome.ofMargin (margin R a b) :=
  valueAux_eq_ofMargin _ R rfl a b

/-- Each pick is one of the mover's options: its value is at most the margin. -/
theorem le_margin_of_mem {R : Finset ℕ} {x : ℕ} (hx : x ∈ R) (a b : ℕ) :
    (if b ≤ a + x then -margin (R.erase x) b (a + x) else margin (R.erase x) (a + x) b) ≤
      margin R a b := by
  have h : R.Nonempty := ⟨x, hx⟩
  conv_rhs => rw [margin, dif_pos h]
  exact Finset.le_sup'_of_le _ (Finset.mem_attach R ⟨x, hx⟩) le_rfl

/-- **Two-token lemma** (C38): at a tie with scores `s`, for openings `y < t` of `S`, the
opponent's margins after them sum to at least 0: after `t` it may take `y` and stay behind by
`t - y`, after `y` it may take `t` and lead by `t - y`, which reaches the same position with the
roles swapped. -/
theorem margin_two_token {S : Finset ℕ} {y t : ℕ} (hy : y ∈ S) (ht : t ∈ S) (hyt : y < t)
    (s : ℕ) : 0 ≤ margin (S.erase t) s (s + t) + margin (S.erase y) s (s + y) := by
  have hy' : y ∈ S.erase t := Finset.mem_erase.mpr ⟨hyt.ne, hy⟩
  have ht' : t ∈ S.erase y := Finset.mem_erase.mpr ⟨hyt.ne', ht⟩
  have h1 := le_margin_of_mem hy' s (s + t)
  have h2 := le_margin_of_mem ht' s (s + y)
  rw [if_neg (show ¬(s + t ≤ s + y) by omega)] at h1
  rw [if_pos (show s + y ≤ s + t by omega), Finset.erase_right_comm] at h2
  linarith

/-- A maximum of numbers of one parity has that parity. -/
private theorem even_sup'_add_of {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (F : ι → ℤ)
    (c : ℤ) (h : ∀ i ∈ s, Even (F i + c)) : Even (s.sup' hs F + c) := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hs F
  rw [he]; exact h i hi

/-- The margin has the parity of `a + b + ∑ R`: the two final scores sum to `a + b + ∑ R`. -/
theorem even_margin_add (n : ℕ) : ∀ (R : Finset ℕ), R.card = n → ∀ a b : ℕ,
    Even (margin R a b + a + b + ∑ x ∈ R, (x : ℤ)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hn a b
  subst hn
  by_cases h : R.Nonempty
  · rw [margin, dif_pos h, add_assoc, add_assoc]
    apply even_sup'_add_of
    rintro ⟨x, hx⟩ -
    try dsimp only
    have hlt : (R.erase x).card < R.card := Finset.card_erase_lt_of_mem hx
    have hs : ∑ y ∈ R.erase x, (y : ℤ) + x = ∑ y ∈ R, (y : ℤ) := Finset.sum_erase_add R _ hx
    by_cases hc : b ≤ a + x
    · rw [if_pos hc]
      have := ih _ hlt (R.erase x) rfl b (a + x)
      rw [Int.even_iff] at this ⊢
      push_cast at this
      omega
    · rw [if_neg hc]
      have := ih _ hlt (R.erase x) rfl (a + x) b
      rw [Int.even_iff] at this ⊢
      push_cast at this
      omega
  · have h0 : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    subst h0
    rw [margin, dif_neg Finset.not_nonempty_empty]
    simp only [Finset.sum_empty, add_zero]
    exact ⟨a, by ring⟩

private theorem sum_Icc_mul_two (N : ℕ) : (∑ x ∈ Finset.Icc 1 N, x) * 2 = N * (N + 1) := by
  induction N with
  | zero => first | rfl | decide | simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), add_mul, ih]
    ring

/-- **C37 (3)**: if the starting margin of `{1..N}` is at most 1 in absolute value for every
even total, the conjecture holds: an even total makes the margin even, hence 0, a draw. -/
theorem conjecture_of_margin_le_one
    (h : ∀ N : ℕ, Even (N * (N + 1) / 2) → |margin (Finset.Icc 1 N) 0 0| ≤ 1) : Conjecture := by
  intro N hN
  have hS : ∑ x ∈ Finset.Icc 1 N, x = N * (N + 1) / 2 :=
    (Nat.div_eq_of_eq_mul_left (by norm_num) (sum_Icc_mul_two N).symm).symm
  have hpar := even_margin_add _ (Finset.Icc 1 N) rfl 0 0
  have hcast : ∑ x ∈ Finset.Icc 1 N, (x : ℤ) = ((N * (N + 1) / 2 : ℕ) : ℤ) := by
    rw [← hS, Nat.cast_sum]
  rw [hcast] at hpar
  have hE : Even ((N * (N + 1) / 2 : ℕ) : ℤ) := (Int.even_coe_nat _).mpr hN
  have hm := h N hN
  have h0 : margin (Finset.Icc 1 N) 0 0 = 0 := by
    generalize ((N * (N + 1) / 2 : ℕ) : ℤ) = X at hpar hE
    rw [Int.even_iff] at hpar hE
    rw [abs_le] at hm
    simp only [Nat.cast_zero, add_zero] at hpar
    omega
  rw [value, valueAux_true_eq_false, valueAux_eq_ofMargin', h0]
  simp [Outcome.ofMargin]

end CatchUp
