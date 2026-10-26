module

public import CatchUp.Best

/-!
# High sets are the rounds game

Blueprint L13. On offsets `O` placed high enough, `{a + o : o ∈ O}` with `a > d + ∑ O`, every pick
of a player at most `d + ∑ O` behind catches up, and the other player catches up with at most two
picks. So play goes in rounds of one pick each, the player behind picking first: the rounds game
`roundsValue`.
-/

@[expose] public section

namespace CatchUp

/-- The rounds game (blueprint L13): the value for the mover, trailing by `d`, on offsets `O`.
The mover picks `i`, the other player answers `j`; the mover then trails by `d + j - i` and moves
again if that is `≥ 0`, else the other player moves, trailing by `i - d - j`. An empty set is a
draw at debt 0 and a loss otherwise. With no answer left (odd `O`) the mover wins; L13 assumes
`O` even. -/
noncomputable def roundsValue (O : Finset ℕ) (d : ℕ) : Outcome :=
  if O = ∅ then (if d = 0 then .draw else .loss)
  else
    Outcome.best (O.attach.toList.map fun ⟨i, _⟩ =>
      (Outcome.best ((O.erase i).attach.toList.map fun ⟨j, _⟩ =>
        if i ≤ d + j then (roundsValue ((O.erase i).erase j) (d + j - i)).neg
        else roundsValue ((O.erase i).erase j) (i - d - j))).neg)
termination_by O.card
decreasing_by
  all_goals
    exact lt_trans (Finset.card_erase_lt_of_mem ‹_›) (Finset.card_erase_lt_of_mem ‹_›)

theorem roundsValue_empty (d : ℕ) : roundsValue ∅ d = if d = 0 then .draw else .loss := by
  rw [roundsValue]; simp

/-- `best` depends only on which outcomes occur (L6). -/
theorem Outcome.best_congr {l₁ l₂ : List Outcome} (h : ∀ o, o ∈ l₁ ↔ o ∈ l₂) :
    Outcome.best l₁ = Outcome.best l₂ := by
  by_cases hw : Outcome.win ∈ l₁
  · rw [(Outcome.best_eq_win_iff l₁).2 hw, (Outcome.best_eq_win_iff l₂).2 ((h _).1 hw)]
  · have hw' : Outcome.win ∉ l₂ := fun h' => hw ((h _).2 h')
    by_cases hd : Outcome.draw ∈ l₁
    · rw [(Outcome.best_eq_draw_iff l₁).2 ⟨hd, hw⟩,
        (Outcome.best_eq_draw_iff l₂).2 ⟨(h _).1 hd, hw'⟩]
    · have hd' : Outcome.draw ∉ l₂ := fun h' => hd ((h _).2 h')
      rw [(Outcome.best_eq_loss_iff l₁).2 ⟨hw, hd⟩, (Outcome.best_eq_loss_iff l₂).2 ⟨hw', hd'⟩]

private theorem sum_map_add (O : Finset ℕ) (a : ℕ) :
    ∑ x ∈ O.map (addLeftEmbedding a), x = O.card * a + ∑ o ∈ O, o := by
  rw [Finset.sum_map]
  simp only [addLeftEmbedding_apply]
  rw [Finset.sum_add_distrib, Finset.sum_const]
  rfl

private theorem map_erase_add (O : Finset ℕ) (a i : ℕ) :
    (O.map (addLeftEmbedding a)).erase (a + i) = (O.erase i).map (addLeftEmbedding a) := by
  rw [Finset.map_erase]; rfl

/-- The other player's node: after the mover's pick `a + i`, it trails by `a + i - d`. -/
theorem valueAux_answer (O : Finset ℕ) (hO : Even O.card) (a d : ℕ)
    (ha : d + ∑ o ∈ O, o < a) (s i : ℕ) (hi : i ∈ O)
    (ih : ∀ O' : Finset ℕ, O'.card < O.card → Even O'.card → ∀ d', d' + ∑ o ∈ O', o < a →
      ∀ s', valueAux (O'.map (addLeftEmbedding a)) s' (s' + d') false = roundsValue O' d') :
    valueAux ((O.map (addLeftEmbedding a)).erase (a + i)) (s + d) (s + (a + i)) false =
      Outcome.best ((O.erase i).attach.toList.map fun ⟨j, _⟩ =>
        if i ≤ d + j then (roundsValue ((O.erase i).erase j) (d + j - i)).neg
        else roundsValue ((O.erase i).erase j) (i - d - j)) := by
  have hsumO : ∑ o ∈ O.erase i, o + i = ∑ o ∈ O, o := Finset.sum_erase_add O _ hi
  have hcardO : (O.erase i).card + 1 = O.card := Finset.card_erase_add_one hi
  have hne : O.erase i ≠ ∅ := by
    intro h0
    rw [h0, Finset.card_empty] at hcardO
    rw [← hcardO] at hO
    obtain ⟨k, hk⟩ := hO
    omega
  rw [map_erase_add, valueAux]
  have hne' : (O.erase i).map (addLeftEmbedding a) ≠ ∅ := fun h => hne (Finset.map_eq_empty.mp h)
  simp only [hne', ite_false]
  rw [sum_map_add]
  by_cases hl : s + d + ((O.erase i).card * a + ∑ o ∈ O.erase i, o) < s + (a + i)
  · -- Early loss: only one number is left, and it can't catch up.
    simp only [hl, ite_true]
    have hc1 : (O.erase i).card = 1 := by
      have hpos : 0 < (O.erase i).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
      by_contra hc
      have h2 : 2 * a ≤ (O.erase i).card * a := Nat.mul_le_mul_right a (by omega)
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc1
    have hjO : j ∈ O.erase i := by rw [hj]; exact Finset.mem_singleton_self j
    have hsj : ∑ o ∈ O.erase i, o = j := by rw [hj, Finset.sum_singleton]
    have hlt : ¬ i ≤ d + j := by rw [hc1, hsj] at hl; omega
    symm
    rw [Outcome.best_eq_loss_iff]
    constructor <;>
    · intro hmem
      obtain ⟨⟨j', hj'⟩, -, hval⟩ := List.mem_map.mp hmem
      have hjj : j' = j := by rw [hj] at hj'; exact Finset.mem_singleton.mp hj'
      subst hjj
      have hempty : (O.erase i).erase j' = ∅ := by rw [hj]; simp
      have hne0 : i - d - j' ≠ 0 := by omega
      simp [hlt, hempty, roundsValue_empty, hne0] at hval
  · simp only [hl, ite_false]
    apply Outcome.best_congr
    intro o
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and, Subtype.exists,
      Finset.mem_map, addLeftEmbedding_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨j, hj, rfl⟩ := hy
      refine ⟨j, hj, ?_⟩
      have hjO : j ∈ O := Finset.mem_of_mem_erase hj
      have hsum2 : ∑ o ∈ (O.erase i).erase j, o + j = ∑ o ∈ O.erase i, o :=
        Finset.sum_erase_add _ _ hj
      have hcard2 : ((O.erase i).erase j).card + 1 = (O.erase i).card :=
        Finset.card_erase_add_one hj
      have hlt2 : ((O.erase i).erase j).card < O.card := by omega
      have hev2 : Even ((O.erase i).erase j).card := by
        obtain ⟨k, hk⟩ := hO
        exact ⟨k - 1, by omega⟩
      have herase : ((O.erase i).map (addLeftEmbedding a)).erase (a + j) =
          ((O.erase i).erase j).map (addLeftEmbedding a) := map_erase_add _ a j
      simp only [Bool.false_eq_true, ite_false, herase]
      by_cases hc : i ≤ d + j
      · have hge : s + d + (a + j) ≥ s + (a + i) := by omega
        simp only [hc, hge, ite_true]
        rw [show s + d + (a + j) = s + (a + i) + (d + j - i) by omega]
        rw [ih _ hlt2 hev2 _ (by omega)]
      · have hge : ¬ s + d + (a + j) ≥ s + (a + i) := by omega
        simp only [hc, hge, ite_false]
        rw [show s + (a + i) = s + d + (a + j) + (i - d - j) by omega]
        rw [ih _ hlt2 hev2 _ (by omega)]
    · rintro ⟨j, hj, rfl⟩
      refine ⟨a + j, ⟨j, hj, rfl⟩, ?_⟩
      have hsum2 : ∑ o ∈ (O.erase i).erase j, o + j = ∑ o ∈ O.erase i, o :=
        Finset.sum_erase_add _ _ hj
      have hcard2 : ((O.erase i).erase j).card + 1 = (O.erase i).card :=
        Finset.card_erase_add_one hj
      have hlt2 : ((O.erase i).erase j).card < O.card := by omega
      have hev2 : Even ((O.erase i).erase j).card := by
        obtain ⟨k, hk⟩ := hO
        exact ⟨k - 1, by omega⟩
      have herase : ((O.erase i).map (addLeftEmbedding a)).erase (a + j) =
          ((O.erase i).erase j).map (addLeftEmbedding a) := map_erase_add _ a j
      simp only [Bool.false_eq_true, ite_false, herase]
      by_cases hc : i ≤ d + j
      · have hge : s + d + (a + j) ≥ s + (a + i) := by omega
        simp only [hc, hge, ite_true]
        rw [show s + d + (a + j) = s + (a + i) + (d + j - i) by omega]
        rw [ih _ hlt2 hev2 _ (by omega)]
      · have hge : ¬ s + d + (a + j) ≥ s + (a + i) := by omega
        simp only [hc, hge, ite_false]
        rw [show s + (a + i) = s + d + (a + j) + (i - d - j) by omega]
        rw [ih _ hlt2 hev2 _ (by omega)]

/-- **L13.** On `{a + o : o ∈ O}` with `O` even and `d + ∑ O < a`, the mover trailing by `d`
(outside the opening) has the rounds-game value. -/
theorem valueAux_map_add (O : Finset ℕ) (hO : Even O.card) (a d : ℕ)
    (ha : d + ∑ o ∈ O, o < a) (s : ℕ) :
    valueAux (O.map (addLeftEmbedding a)) s (s + d) false = roundsValue O d := by
  induction hn : O.card using Nat.strong_induction_on generalizing O d s with
  | _ n ih =>
  subst hn
  by_cases h0 : O = ∅
  · subst h0
    rw [valueAux, roundsValue_empty]
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · have h1 : ¬ s > s + d := by omega
      have h2 : s + d > s := by omega
      simp [h1, h2, Nat.pos_iff_ne_zero.mp hd]
  · rw [valueAux, roundsValue]
    have hne' : O.map (addLeftEmbedding a) ≠ ∅ := fun h => h0 (Finset.map_eq_empty.mp h)
    have hpos : 0 < O.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
    have hnl : ¬ s + ∑ x ∈ O.map (addLeftEmbedding a), x < s + d := by
      rw [sum_map_add]
      have : a ≤ O.card * a := Nat.le_mul_of_pos_left a hpos
      omega
    simp only [hne', h0, hnl, ite_false]
    apply Outcome.best_congr
    intro o
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_attach, true_and, Subtype.exists,
      Finset.mem_map, addLeftEmbedding_apply]
    have hih : ∀ O' : Finset ℕ, O'.card < O.card → Even O'.card → ∀ d', d' + ∑ o ∈ O', o < a →
        ∀ s', valueAux (O'.map (addLeftEmbedding a)) s' (s' + d') false = roundsValue O' d' :=
      fun O' h1 h2 d' h3 s' => ih _ h1 O' h2 d' h3 s' rfl
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨i, hi, ?_⟩
      have hle : i ≤ ∑ o ∈ O, o := by have := Finset.sum_erase_add O (fun o => o) hi; omega
      have hge : s + (a + i) ≥ s + d := by omega
      simp only [Bool.false_eq_true, ite_false, hge, ite_true]
      rw [valueAux_answer O hO a d ha s i hi hih]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨a + i, ⟨i, hi, rfl⟩, ?_⟩
      have hle : i ≤ ∑ o ∈ O, o := by have := Finset.sum_erase_add O (fun o => o) hi; omega
      have hge : s + (a + i) ≥ s + d := by omega
      simp only [Bool.false_eq_true, ite_false, hge, ite_true]
      rw [valueAux_answer O hO a d ha s i hi hih]

end CatchUp
