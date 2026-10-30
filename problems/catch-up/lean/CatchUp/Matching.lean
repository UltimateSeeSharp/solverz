module

public import CatchUp.Potential

/-!
# The matching bound

Claim C20.

`matchCost O` pairs the two smallest numbers, then recurses: `(o₂ - o₁) + (o₄ - o₃) + ⋯`. A mover
trailing by more than it loses the rounds game: the other player answers each pick with its partner
(`roundsMargin_le_matchCost`).
-/

@[expose] public section

namespace CatchUp

/-- Bottom-up matching cost `(o₂ - o₁) + (o₄ - o₃) + ⋯` of a finite set sorted increasingly. -/
noncomputable def matchCost (O : Finset ℕ) : ℤ :=
  if h : O.Nonempty then
    if h' : (O.erase (O.min' h)).Nonempty then
      (((O.erase (O.min' h)).min' h' : ℕ) : ℤ) - (O.min' h : ℕ) +
        matchCost ((O.erase (O.min' h)).erase ((O.erase (O.min' h)).min' h'))
    else 0
  else 0
termination_by O.card
decreasing_by
  exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem (Finset.min'_mem _ h')) Finset.card_erase_le

theorem matchCost_empty : matchCost ∅ = 0 := by
  rw [matchCost]; simp

/-- Unfolding at the two smallest numbers `a < b`. -/
theorem matchCost_of_min {O : Finset ℕ} {a b : ℕ} (ha : a ∈ O) (hb : b ∈ O) (hab : a < b)
    (hmin : ∀ x ∈ O, x = a ∨ b ≤ x) :
    matchCost O = (b : ℤ) - a + matchCost ((O.erase a).erase b) := by
  have h : O.Nonempty := ⟨a, ha⟩
  have hm : O.min' h = a :=
    le_antisymm (Finset.min'_le O a ha) (Finset.le_min' O h a fun x hx => by
      rcases hmin x hx with rfl | hx' <;> omega)
  have hbE : b ∈ O.erase a := Finset.mem_erase.mpr ⟨by omega, hb⟩
  have h' : (O.erase (O.min' h)).Nonempty := hm ▸ ⟨b, hbE⟩
  have hm' : (O.erase (O.min' h)).min' h' = b := by
    apply le_antisymm (Finset.min'_le _ b (hm ▸ hbE))
    apply Finset.le_min'
    intro x hx
    rw [hm] at hx
    rcases hmin x (Finset.mem_of_mem_erase hx) with rfl | hx'
    · exact absurd rfl (Finset.mem_erase.mp hx).1
    · exact hx'
  rw [matchCost]
  simp only [h, ↓reduceDIte, h']
  rw [hm']
  simp only [hm]

theorem matchCost_nonneg (n : ℕ) : ∀ O : Finset ℕ, O.card = n → 0 ≤ matchCost O := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro O hn
  rw [matchCost]
  split_ifs with h h'
  · have hlt : ((O.erase (O.min' h)).erase ((O.erase (O.min' h)).min' h')).card < n :=
      hn ▸ lt_of_lt_of_le (Finset.card_erase_lt_of_mem (Finset.min'_mem _ h')) Finset.card_erase_le
    have h1 := ih _ hlt _ rfl
    have h2 : O.min' h ≤ (O.erase (O.min' h)).min' h' :=
      Finset.min'_le O _ (Finset.mem_of_mem_erase (Finset.min'_mem _ h'))
    have h2' : ((O.min' h : ℕ) : ℤ) ≤ ((O.erase (O.min' h)).min' h' : ℕ) := by exact_mod_cast h2
    linarith
  · exact le_refl _
  · exact le_refl _

/-- Every number has a partner whose removal lowers the matching cost by at least their distance. -/
theorem exists_partner (n : ℕ) : ∀ O : Finset ℕ, O.card = n → Even n → ∀ i ∈ O,
    ∃ j ∈ O.erase i, matchCost ((O.erase i).erase j) + |(i : ℤ) - j| ≤ matchCost O := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro O hn hev i hi
  have h : O.Nonempty := ⟨i, hi⟩
  set a := O.min' h with ha_def
  have ha : a ∈ O := Finset.min'_mem O h
  have h' : (O.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have := Finset.card_erase_add_one ha
    rw [he, Finset.card_empty] at this
    obtain ⟨k, hk⟩ := hev
    omega
  set b := (O.erase a).min' h' with hb_def
  have hbE : b ∈ O.erase a := Finset.min'_mem _ h'
  have hb : b ∈ O := Finset.mem_of_mem_erase hbE
  have hba : b ≠ a := (Finset.mem_erase.mp hbE).1
  have hab : a < b := lt_of_le_of_ne (Finset.min'_le O b hb) (Ne.symm hba)
  have hmin : ∀ x ∈ O, x = a ∨ b ≤ x := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (Finset.min'_le _ x (Finset.mem_erase.mpr ⟨hxa, hx⟩))
  have hc := matchCost_of_min ha hb hab hmin
  have hab' : (a : ℤ) < b := by exact_mod_cast hab
  by_cases hia : i = a
  · refine ⟨b, by rw [hia]; exact hbE, ?_⟩
    rw [hia, hc, abs_of_neg (sub_neg.mpr hab')]
    linarith
  by_cases hib : i = b
  · refine ⟨a, by rw [hib]; exact Finset.mem_erase.mpr ⟨Ne.symm hba, ha⟩, ?_⟩
    rw [hib, hc, Finset.erase_right_comm, abs_of_pos (sub_pos.mpr hab')]
    linarith
  -- `i` lies above the two smallest: use the partner inside the rest.
  have hiR : i ∈ (O.erase a).erase b := Finset.mem_erase.mpr ⟨hib, Finset.mem_erase.mpr ⟨hia, hi⟩⟩
  have hcard : ((O.erase a).erase b).card + 2 = n := by
    have h1 := Finset.card_erase_add_one ha
    have h2 := Finset.card_erase_add_one hbE
    omega
  have hevR : Even ((O.erase a).erase b).card := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  obtain ⟨j, hj, hjc⟩ := ih _ (by omega) _ rfl hevR i hiR
  have hjR : j ∈ (O.erase a).erase b := Finset.mem_of_mem_erase hj
  have hja : j ≠ a := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hjR)).1
  have hjb : j ≠ b := (Finset.mem_erase.mp hjR).1
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hjO : j ∈ O := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hjR)
  refine ⟨j, Finset.mem_erase.mpr ⟨hji, hjO⟩, ?_⟩
  have haP : a ∈ (O.erase i).erase j :=
    Finset.mem_erase.mpr ⟨Ne.symm hja, Finset.mem_erase.mpr ⟨Ne.symm hia, ha⟩⟩
  have hbP : b ∈ (O.erase i).erase j :=
    Finset.mem_erase.mpr ⟨Ne.symm hjb, Finset.mem_erase.mpr ⟨Ne.symm hib, hb⟩⟩
  have hc' := matchCost_of_min haP hbP hab fun x hx =>
    hmin x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
  have hset : (((O.erase i).erase j).erase a).erase b =
      (((O.erase a).erase b).erase i).erase j := by
    ext x
    simp only [Finset.mem_erase]
    tauto
  rw [hc', hset, hc]
  linarith

/-- **C20.** A mover trailing by more than the matching cost loses by at least the difference. -/
theorem roundsMargin_le_matchCost (n : ℕ) : ∀ O : Finset ℕ, O.card = n → Even n → ∀ d : ℕ,
    matchCost O < d → roundsMargin O d ≤ matchCost O - d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro O hn hev d hd
  by_cases h0 : O = ∅
  · subst h0
    rw [roundsMargin, matchCost_empty]
    simp
  have hne : O.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
  have key := roundsMargin_le_neg (hn ▸ hev) hne d ((d : ℤ) - matchCost O) ?_
  · linarith
  intro i hi
  obtain ⟨j, hj, hjc⟩ := exists_partner n O hn hev i hi
  refine ⟨j, hj, ?_⟩
  have hcard : ((O.erase i).erase j).card + 2 = n := by
    have h1 := Finset.card_erase_add_one hi
    have h2 := Finset.card_erase_add_one hj
    omega
  have hev2 : Even ((O.erase i).erase j).card := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  have hnn := matchCost_nonneg _ ((O.erase i).erase j) rfl
  have habs := le_abs_self ((i : ℤ) - j)
  have habs' := neg_abs_le ((i : ℤ) - j)
  have hc : i ≤ d + j := by
    have : (i : ℤ) < d + j := by linarith
    omega
  simp only [hc, ite_true]
  have hδ : (((d + j - i : ℕ)) : ℤ) = d + j - i := by rw [Nat.cast_sub hc]; push_cast; ring
  have hIH := ih _ (by omega) _ rfl hev2 (d + j - i) (by rw [hδ]; linarith)
  rw [hδ] at hIH
  linarith

end CatchUp
