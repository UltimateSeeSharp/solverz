module

public import CatchUp.Rounds
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Margins in the rounds game

The rounds game (`roundsValue`, blueprint L13) scores only win, draw or loss. `roundsMargin` is
the minimax final margin instead: the mover's total minus the other player's, minus its debt.
Since the outcome is the sign of the margin and the sign is monotone, the value is the sign of the
minimax margin (`roundsValue_eq_ofMargin`), so a strategy that guarantees a margin bounds the value.
The margin has the parity of `∑ O + d` (`even_roundsMargin_add`).
-/

@[expose] public section

namespace CatchUp

/-- The outcome of a final margin: win if positive, loss if negative, draw at 0. -/
def Outcome.ofMargin (m : ℤ) : Outcome :=
  if 0 < m then .win else if m < 0 then .loss else .draw

theorem Outcome.ofMargin_neg (m : ℤ) : (Outcome.ofMargin m).neg = Outcome.ofMargin (-m) := by
  unfold Outcome.ofMargin
  by_cases h1 : 0 < m
  · simp [h1, Outcome.neg, not_lt.mpr (le_of_lt h1)]
  · by_cases h2 : m < 0
    · simp [h1, h2, Outcome.neg]
    · have : m = 0 := by linarith [not_lt.mp h1, not_lt.mp h2]
      subst this; simp [Outcome.neg]

/-- The minimax final margin of the rounds game for the mover, trailing by `d`: the maximum over
its picks `i` of minus the other player's best margin over its answers `j`. With no answer left
(odd `O`) the mover takes `i` last. -/
noncomputable def roundsMargin (O : Finset ℕ) (d : ℕ) : ℤ :=
  if h : O.Nonempty then
    O.attach.sup' (by simpa using h) fun i =>
      if h' : (O.erase i.1).Nonempty then
        -((O.erase i.1).attach.sup' (by simpa using h') fun j =>
          if i.1 ≤ d + j.1 then -roundsMargin ((O.erase i.1).erase j.1) (d + j.1 - i.1)
          else roundsMargin ((O.erase i.1).erase j.1) (i.1 - d - j.1))
      else (i.1 : ℤ) - d
  else -(d : ℤ)
termination_by O.card
decreasing_by
  all_goals exact lt_trans (Finset.card_erase_lt_of_mem j.2) (Finset.card_erase_lt_of_mem i.2)

/-- `best` of the outcomes of a family of margins is the outcome of their maximum. -/
theorem Outcome.best_eq_ofMargin_sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (F : ι → ℤ)
    (l : List Outcome) (hl : ∀ o, o ∈ l ↔ ∃ i ∈ s, o = Outcome.ofMargin (F i)) :
    Outcome.best l = Outcome.ofMargin (s.sup' hs F) := by
  obtain ⟨i0, hi0, hM⟩ := Finset.exists_mem_eq_sup' hs F
  have hle : ∀ i ∈ s, F i ≤ s.sup' hs F := fun i hi => Finset.le_sup' F hi
  rw [hM] at hle ⊢
  have hmem0 : Outcome.ofMargin (F i0) ∈ l := (hl _).2 ⟨i0, hi0, rfl⟩
  by_cases h1 : 0 < F i0
  · have hw : Outcome.ofMargin (F i0) = .win := by simp [Outcome.ofMargin, h1]
    rw [hw, (Outcome.best_eq_win_iff l).2 (hw ▸ hmem0)]
  · have hnw : Outcome.win ∉ l := by
      intro hw
      obtain ⟨i, hi, he⟩ := (hl _).1 hw
      have := hle i hi
      unfold Outcome.ofMargin at he
      split_ifs at he
      omega
    by_cases h2 : F i0 < 0
    · have hl' : Outcome.ofMargin (F i0) = .loss := by simp [Outcome.ofMargin, h1, h2]
      rw [hl', (Outcome.best_eq_loss_iff l).2 ⟨hnw, ?_⟩]
      intro hd
      obtain ⟨i, hi, he⟩ := (hl _).1 hd
      have := hle i hi
      unfold Outcome.ofMargin at he
      split_ifs at he
      omega
    · have hd : Outcome.ofMargin (F i0) = .draw := by simp [Outcome.ofMargin, h1, h2]
      rw [hd, (Outcome.best_eq_draw_iff l).2 ⟨hd ▸ hmem0, hnw⟩]

/-- The other player's answers to the mover's pick `i`, as outcomes: the sign of their margins. -/
private theorem inner_eq (O : Finset ℕ) (d i : ℕ) (hi : i ∈ O) (h' : (O.erase i).Nonempty)
    (ih : ∀ O' : Finset ℕ, O'.card < O.card → Even O'.card → ∀ d',
      roundsValue O' d' = Outcome.ofMargin (roundsMargin O' d'))
    (hev : Even O.card) :
    Outcome.best ((O.erase i).attach.toList.map fun ⟨j, _⟩ =>
        if i ≤ d + j then (roundsValue ((O.erase i).erase j) (d + j - i)).neg
        else roundsValue ((O.erase i).erase j) (i - d - j)) =
      Outcome.ofMargin ((O.erase i).attach.sup' (by simpa using h') fun j =>
        if i ≤ d + j.1 then -roundsMargin ((O.erase i).erase j.1) (d + j.1 - i)
        else roundsMargin ((O.erase i).erase j.1) (i - d - j.1)) := by
  apply Outcome.best_eq_ofMargin_sup'
  intro o
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and]
  have key : ∀ j (hj : j ∈ O.erase i),
      (if i ≤ d + j then (roundsValue ((O.erase i).erase j) (d + j - i)).neg
        else roundsValue ((O.erase i).erase j) (i - d - j)) =
      Outcome.ofMargin (if i ≤ d + j then -roundsMargin ((O.erase i).erase j) (d + j - i)
        else roundsMargin ((O.erase i).erase j) (i - d - j)) := by
    intro j hj
    have hc1 : (O.erase i).card + 1 = O.card := Finset.card_erase_add_one hi
    have hc2 : ((O.erase i).erase j).card + 1 = (O.erase i).card := Finset.card_erase_add_one hj
    have hev2 : Even ((O.erase i).erase j).card := by
      obtain ⟨k, hk⟩ := hev
      exact ⟨k - 1, by omega⟩
    have hlt : ((O.erase i).erase j).card < O.card := by omega
    by_cases hc : i ≤ d + j
    · simp only [hc, ite_true, ih _ hlt hev2, Outcome.ofMargin_neg]
    · simp only [hc, ite_false, ih _ hlt hev2]
  constructor
  · rintro ⟨⟨j, hj⟩, rfl⟩
    exact ⟨⟨j, hj⟩, key j hj⟩
  · rintro ⟨⟨j, hj⟩, rfl⟩
    exact ⟨⟨j, hj⟩, key j hj⟩

/-- An even set has an answer to every pick. -/
private theorem erase_nonempty_of_even {O : Finset ℕ} (hev : Even O.card) {i : ℕ} (hi : i ∈ O) :
    (O.erase i).Nonempty := by
  by_contra hc
  have h1 := Finset.card_erase_add_one hi
  rw [Finset.not_nonempty_iff_eq_empty.mp hc, Finset.card_empty] at h1
  obtain ⟨k, hk⟩ := hev
  omega

/-- The value of the rounds game on an even set is the sign of its minimax margin. -/
theorem roundsValue_eq_ofMargin (n : ℕ) : ∀ (O : Finset ℕ), O.card = n → Even n → ∀ d,
    roundsValue O d = Outcome.ofMargin (roundsMargin O d) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro O hn hev d
  subst hn
  have ih' : ∀ O' : Finset ℕ, O'.card < O.card → Even O'.card → ∀ d',
      roundsValue O' d' = Outcome.ofMargin (roundsMargin O' d') :=
    fun O' h1 h2 d' => ih _ h1 O' rfl h2 d'
  by_cases h0 : O = ∅
  · subst h0
    rw [roundsValue_empty, roundsMargin]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp [Outcome.ofMargin]
    · have hd' : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd
      have : (0 : ℤ) < d := by exact_mod_cast hd
      simp [Outcome.ofMargin, hd', hd, not_lt.mpr this.le]
  · have hne : O.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    rw [roundsValue, roundsMargin]
    simp only [h0, ite_false, hne, ↓reduceDIte]
    apply Outcome.best_eq_ofMargin_sup'
    intro o
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      simp only [erase_nonempty_of_even hev hi, ↓reduceDIte]
      rw [inner_eq O d i hi (erase_nonempty_of_even hev hi) ih' hev, Outcome.ofMargin_neg]
    · rintro ⟨⟨i, hi⟩, rfl⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      simp only [erase_nonempty_of_even hev hi, ↓reduceDIte]
      rw [inner_eq O d i hi (erase_nonempty_of_even hev hi) ih' hev, Outcome.ofMargin_neg]

/-- A maximum of numbers of one parity has that parity. -/
private theorem even_sup'_add {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (F : ι → ℤ) (c : ℤ)
    (h : ∀ i ∈ s, Even (F i + c)) : Even (s.sup' hs F + c) := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup' hs F
  rw [he]; exact h i hi

/-- The minimax margin has the parity of `∑ O + d`: every final margin does. -/
theorem even_roundsMargin_add (n : ℕ) : ∀ (O : Finset ℕ), O.card = n → Even n → ∀ d,
    Even (roundsMargin O d + d + ∑ o ∈ O, (o : ℤ)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro O hn hev d
  subst hn
  by_cases h0 : O = ∅
  · subst h0
    rw [roundsMargin]
    simp
  · have hne : O.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    rw [roundsMargin]
    simp only [hne, ↓reduceDIte]
    rw [add_assoc]
    apply even_sup'_add
    rintro ⟨i, hi⟩ -
    have h' := erase_nonempty_of_even hev hi
    simp only [h', ↓reduceDIte]
    rw [show ∀ x c : ℤ, -x + c = -(x + -c) from fun x c => by ring, even_neg]
    apply even_sup'_add
    rintro ⟨j, hj⟩ -
    have hc1 : (O.erase i).card + 1 = O.card := Finset.card_erase_add_one hi
    have hc2 : ((O.erase i).erase j).card + 1 = (O.erase i).card := Finset.card_erase_add_one hj
    have hev2 : Even ((O.erase i).erase j).card := by
      obtain ⟨k, hk⟩ := hev
      exact ⟨k - 1, by omega⟩
    have hlt : ((O.erase i).erase j).card < O.card := by omega
    have hs1 : ∑ o ∈ (O.erase i), (o : ℤ) + i = ∑ o ∈ O, (o : ℤ) := Finset.sum_erase_add O _ hi
    have hs2 : ∑ o ∈ (O.erase i).erase j, (o : ℤ) + j = ∑ o ∈ O.erase i, (o : ℤ) :=
      Finset.sum_erase_add _ _ hj
    by_cases hc : i ≤ d + j
    · simp only [hc, ite_true]
      have := ih _ hlt _ rfl hev2 (d + j - i)
      rw [Int.even_iff] at this ⊢
      push_cast [hc] at this ⊢
      omega
    · simp only [hc, ite_false]
      have := ih _ hlt _ rfl hev2 (i - d - j)
      have hc' : d + j ≤ i := by omega
      rw [Int.even_iff] at this ⊢
      push_cast [hc', Nat.sub_sub] at this ⊢
      omega

end CatchUp
