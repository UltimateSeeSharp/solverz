module

public import CatchUp.Margin
public import CatchUp.AltSum

/-!
# The catch-up potential bounds always-max with the tie rule

Blueprint L18 and its use. Z plays AM+T: as first picker the largest number left; as second
picker the largest unless that gives an exact tie, then the second largest. With `c = altSum T`,
the potential is `min (c - d) 0` when Z moves trailing by `d`, and `max (e - c) 0` when the
opponent moves trailing by `e`. If a class of states is closed under AM+T's rounds and, wherever
the opponent moves, its lead `e` is at least `(t₁ - t₂) - altSum (T \ {t₁, t₂})` (at least
`t₁ - t₂ - 1` with two numbers left), then Z's minimax margin is at least the potential minus one
(`potential_le_roundsMargin`).
-/

@[expose] public section

namespace CatchUp

/-- A number removed below the maximum leaves a smaller maximum. -/
theorem max'_erase_max'_lt {W : Finset ℕ} (h : W.Nonempty) (h' : (W.erase (W.max' h)).Nonempty) :
    (W.erase (W.max' h)).max' h' < W.max' h := by
  apply lt_of_le_of_ne
  · exact Finset.max'_le _ _ _ fun y hy => Finset.le_max' W y (Finset.mem_of_mem_erase hy)
  · exact fun he => (Finset.notMem_erase _ W) (he ▸ Finset.max'_mem _ h')

theorem altSum_nonneg_and_le (n : ℕ) : ∀ (W : Finset ℕ), W.card = n → 0 ≤ altSum W ∧
    ∀ h : W.Nonempty, altSum W ≤ W.max' h := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn
  by_cases h : W.Nonempty
  · have hlt : (W.erase (W.max' h)).card < n :=
      hn ▸ Finset.card_erase_lt_of_mem (Finset.max'_mem W h)
    obtain ⟨h1, h2⟩ := ih _ hlt _ rfl
    rw [altSum_of_nonempty h]
    refine ⟨?_, fun h'' => ?_⟩
    · by_cases h' : (W.erase (W.max' h)).Nonempty
      · have h3 := h2 h'
        have hm : ((W.erase (W.max' h)).max' h' : ℤ) < W.max' h := by
          exact_mod_cast max'_erase_max'_lt h h'
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp h', altSum_empty]
        simp
    · have : W.max' h'' = W.max' h := rfl
      rw [this]
      linarith
  · rw [altSum]
    simp only [h, ↓reduceDIte]
    exact ⟨le_refl _, fun h' => h'.elim⟩

theorem altSum_nonneg (W : Finset ℕ) : 0 ≤ altSum W := (altSum_nonneg_and_le _ W rfl).1

theorem altSum_le_max' (W : Finset ℕ) (h : W.Nonempty) : altSum W ≤ W.max' h :=
  (altSum_nonneg_and_le _ W rfl).2 h

/-- The mover picks `i`: if every answer `j` leaves the other player at most `B`, the mover's
minimax margin is at least `-B`. -/
theorem neg_le_roundsMargin {T : Finset ℕ} (hev : Even T.card) (d : ℕ) {i : ℕ} (hi : i ∈ T)
    (B : ℤ) (h : ∀ j ∈ T.erase i, (if i ≤ d + j then -roundsMargin ((T.erase i).erase j) (d + j - i)
      else roundsMargin ((T.erase i).erase j) (i - d - j)) ≤ B) :
    -B ≤ roundsMargin T d := by
  have hne : T.Nonempty := ⟨i, hi⟩
  have h' := erase_nonempty_of_even hev hi
  rw [roundsMargin]
  simp only [hne, ↓reduceDIte]
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_attach T ⟨i, hi⟩))
  dsimp only
  simp only [h', ↓reduceDIte]
  apply neg_le_neg
  apply Finset.sup'_le
  rintro ⟨j, hj⟩ -
  exact h j hj

/-- If every pick `i` of the mover has an answer `j` giving the other player at least `B`, the
mover's minimax margin is at most `-B`. -/
theorem roundsMargin_le_neg {T : Finset ℕ} (hev : Even T.card) (hne : T.Nonempty) (e : ℕ) (B : ℤ)
    (h : ∀ i ∈ T, ∃ j ∈ T.erase i, B ≤ (if i ≤ e + j then -roundsMargin ((T.erase i).erase j)
      (e + j - i) else roundsMargin ((T.erase i).erase j) (i - e - j))) :
    roundsMargin T e ≤ -B := by
  rw [roundsMargin]
  simp only [hne, ↓reduceDIte]
  apply Finset.sup'_le
  rintro ⟨i, hi⟩ -
  dsimp only
  simp only [erase_nonempty_of_even hev hi, ↓reduceDIte]
  obtain ⟨j, hj, hB⟩ := h i hi
  apply neg_le_neg
  exact Finset.le_sup'_of_le _ (Finset.mem_attach _ ⟨j, hj⟩) hB

/-- AM+T's answer, as second picker leading by `e`, to the opponent's pick `i`, from the numbers
`U` left: the largest, unless that gives an exact tie (`e + m = i`) and another number is left;
then the second largest. -/
noncomputable def amtReply (U : Finset ℕ) (e i : ℕ) : ℕ :=
  if h : U.Nonempty then
    if h' : e + U.max' h = i ∧ (U.erase (U.max' h)).Nonempty then (U.erase (U.max' h)).max' h'.2
    else U.max' h
  else 0

theorem amtReply_mem {U : Finset ℕ} (h : U.Nonempty) (e i : ℕ) : amtReply U e i ∈ U := by
  unfold amtReply
  simp only [h, ↓reduceDIte]
  split_ifs with h'
  · exact Finset.mem_of_mem_erase (Finset.max'_mem _ h'.2)
  · exact Finset.max'_mem _ h

private theorem card_two {T : Finset ℕ} (hev : Even T.card) {a b : ℕ} (ha : a ∈ T)
    (hb : b ∈ T.erase a) :
    ((T.erase a).erase b).card < T.card ∧ Even ((T.erase a).erase b).card ∧
      ((T.erase a).erase b).card + 2 = T.card := by
  have h1 := Finset.card_erase_add_one ha
  have h2 := Finset.card_erase_add_one hb
  obtain ⟨k, hk⟩ := hev
  exact ⟨by omega, ⟨k - 1, by omega⟩, by omega⟩

/-- **L18, used.** Z plays AM+T. `KZ T d`: Z moves trailing by `d`; `KY T e`: the opponent moves
trailing by `e`. If the class is closed under rounds and satisfies the condition wherever the
opponent moves, Z's minimax margin is at least the potential minus one. -/
theorem potential_le_roundsMargin (KZ KY : Finset ℕ → ℕ → Prop)
    (hZ : ∀ T d, KZ T d → ∀ (h : T.Nonempty), ∀ j ∈ T.erase (T.max' h),
      (T.max' h ≤ d + j → KZ ((T.erase (T.max' h)).erase j) (d + j - T.max' h)) ∧
      (¬ T.max' h ≤ d + j → KY ((T.erase (T.max' h)).erase j) (T.max' h - d - j)))
    (hY : ∀ T e, KY T e → ∀ i ∈ T,
      (i ≤ e + amtReply (T.erase i) e i →
        KY ((T.erase i).erase (amtReply (T.erase i) e i)) (e + amtReply (T.erase i) e i - i)) ∧
      (¬ i ≤ e + amtReply (T.erase i) e i →
        KZ ((T.erase i).erase (amtReply (T.erase i) e i)) (i - e - amtReply (T.erase i) e i)))
    (hcond : ∀ T e, KY T e → 4 ≤ T.card → ∀ (h : T.Nonempty) (h' : (T.erase (T.max' h)).Nonempty),
      ((T.max' h : ℤ) - (T.erase (T.max' h)).max' h') -
        altSum ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' h')) ≤ e)
    (hlast : ∀ T e, KY T e → T.card = 2 → ∀ (h : T.Nonempty) (h' : (T.erase (T.max' h)).Nonempty),
      ((T.max' h : ℤ) - (T.erase (T.max' h)).max' h') - 1 ≤ e)
    (n : ℕ) : ∀ T : Finset ℕ, T.card = n → Even n →
      (∀ d, KZ T d → min (altSum T - d) 0 - 1 ≤ roundsMargin T d) ∧
      (∀ e, KY T e → max ((e : ℤ) - altSum T) 0 - 1 ≤ -roundsMargin T e) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn hev
  subst hn
  by_cases h0 : T = ∅
  · subst h0
    refine ⟨fun d _ => ?_, fun e _ => ?_⟩
    · rw [roundsMargin]; simp [altSum_empty]
    · rw [roundsMargin]; simp [altSum_empty]
  have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
  have ht1T : T.max' hne ∈ T := Finset.max'_mem T hne
  have hU : (T.erase (T.max' hne)).Nonempty := erase_nonempty_of_even hev ht1T
  have htop := altSum_top_two hne hU
  have hnn := altSum_nonneg ((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU))
  constructor
  · -- Z moves: it takes the largest number.
    intro d hKZ
    have key := neg_le_roundsMargin hev d ht1T (1 - min (altSum T - d) 0) ?_
    · linarith
    intro j hj
    obtain ⟨hlt2, hev2, -⟩ := card_two hev ht1T hj
    obtain ⟨hIZ, hIY⟩ := ih _ hlt2 _ rfl hev2
    have hr := abs_le.mp (altSum_round hne hj)
    obtain ⟨hK1, hK2⟩ := hZ T d hKZ hne j hj
    by_cases hc : T.max' hne ≤ d + j
    · simp only [hc, ite_true]
      have h1 := hIZ _ (hK1 hc)
      have hcd : altSum T - d ≤ altSum ((T.erase (T.max' hne)).erase j) -
          ((d + j - T.max' hne : ℕ) : ℤ) := by
        rw [Nat.cast_sub hc]; push_cast; linarith [hr.2]
      have hm := min_le_min hcd (le_refl (0 : ℤ))
      linarith
    · simp only [hc, ite_false]
      have h1 := hIY _ (hK2 hc)
      have hm1 := le_max_right (((T.max' hne - d - j : ℕ) : ℤ) -
        altSum ((T.erase (T.max' hne)).erase j)) 0
      have hm2 := min_le_right (altSum T - d) 0
      linarith
  · -- The opponent moves; Z answers with AM+T.
    intro e hKY
    have key := roundsMargin_le_neg hev hne e (max ((e : ℤ) - altSum T) 0 - 1) ?_
    · linarith
    intro i hi
    have hUi := erase_nonempty_of_even hev hi
    refine ⟨amtReply (T.erase i) e i, amtReply_mem hUi e i, ?_⟩
    obtain ⟨hK1, hK2⟩ := hY T e hKY i hi
    obtain ⟨hlt2, hev2, hcard2⟩ := card_two hev hi (amtReply_mem hUi e i)
    obtain ⟨hIZ, hIY⟩ := ih _ hlt2 _ rfl hev2
    by_cases hit : i = T.max' hne
    · -- The opponent takes the largest number.
      subst hit
      by_cases hex : e + (T.erase (T.max' hne)).max' hU = T.max' hne ∧
          ((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).Nonempty
      · -- Exact tie: Z takes the second largest instead.
        have hr : amtReply (T.erase (T.max' hne)) e (T.max' hne) =
            ((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).max' hex.2 := by
          unfold amtReply; simp only [hU, ↓reduceDIte, hex, and_self]
        rw [hr] at hK1 hK2 hIZ hIY ⊢
        have ht32 := max'_erase_max'_lt hU hex.2
        have hc : ¬ T.max' hne ≤ e + ((T.erase (T.max' hne)).erase
            ((T.erase (T.max' hne)).max' hU)).max' hex.2 := by omega
        simp only [hc, ite_false]
        have h1 := hIZ _ (hK2 hc)
        -- The set left after the round has maximum t₂, and below it only numbers under t₃.
        have hne3 : (T.erase (T.max' hne)).max' hU ≠ ((T.erase (T.max' hne)).erase
            ((T.erase (T.max' hne)).max' hU)).max' hex.2 := Nat.ne_of_gt ht32
        have hV : ((T.erase (T.max' hne)).erase (((T.erase (T.max' hne)).erase
            ((T.erase (T.max' hne)).max' hU)).max' hex.2)).Nonempty :=
          ⟨_, Finset.mem_erase.mpr ⟨hne3, Finset.max'_mem _ hU⟩⟩
        have hVmax := max'_erase_of_ne hU (Ne.symm hne3) hV
        have hR : altSum (((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).erase
            (((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).max' hex.2)) ≤
            (((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).max' hex.2 : ℕ) := by
          by_cases hR0 : (((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).erase
              (((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).max' hex.2)).Nonempty
          · have h2 := altSum_le_max' _ hR0
            have h3 := max'_erase_max'_lt hex.2 hR0
            have h3' : ((((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).erase
                (((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).max' hex.2)).max'
                hR0 : ℤ) < (((T.erase (T.max' hne)).erase
                ((T.erase (T.max' hne)).max' hU)).max' hex.2 : ℕ) := by exact_mod_cast h3
            linarith
          · rw [Finset.not_nonempty_iff_eq_empty.mp hR0, altSum_empty]
            positivity
        have hVsum := altSum_of_nonempty hV
        rw [hVmax, Finset.erase_right_comm (s := T.erase (T.max' hne))
          (a := ((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).max' hex.2)]
          at hVsum
        have hδ : (((T.max' hne - e - ((T.erase (T.max' hne)).erase
            ((T.erase (T.max' hne)).max' hU)).max' hex.2 : ℕ)) : ℤ) =
            ((T.erase (T.max' hne)).max' hU : ℤ) - (((T.erase (T.max' hne)).erase
            ((T.erase (T.max' hne)).max' hU)).max' hex.2 : ℕ) := by omega
        have hmin := min_eq_right (show (0 : ℤ) ≤ altSum ((T.erase (T.max' hne)).erase
            (((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU)).max' hex.2)) -
            ((T.max' hne - e - ((T.erase (T.max' hne)).erase
            ((T.erase (T.max' hne)).max' hU)).max' hex.2 : ℕ) : ℤ) by rw [hδ]; linarith)
        have he : (e : ℤ) = (T.max' hne : ℤ) - (T.erase (T.max' hne)).max' hU := by omega
        have hmax := max_eq_right (show (e : ℤ) - altSum T ≤ 0 by linarith)
        linarith
      · have hr : amtReply (T.erase (T.max' hne)) e (T.max' hne) =
            (T.erase (T.max' hne)).max' hU := by
          unfold amtReply; simp only [hU, ↓reduceDIte, hex]
        rw [hr] at hK1 hK2 hIZ hIY hcard2 ⊢
        by_cases hc : T.max' hne ≤ e + (T.erase (T.max' hne)).max' hU
        · simp only [hc, ite_true]
          have h1 := hIY _ (hK1 hc)
          have heq : (((e + (T.erase (T.max' hne)).max' hU - T.max' hne : ℕ) : ℤ) -
              altSum ((T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU))) =
              (e : ℤ) - altSum T := by
            rw [Nat.cast_sub hc]; push_cast; linarith
          rw [heq] at h1
          linarith
        · simp only [hc, ite_false]
          have h1 := hIZ _ (hK2 hc)
          have hmax := max_eq_right (show (e : ℤ) - altSum T ≤ 0 by
            have : (e : ℤ) < (T.max' hne : ℤ) - (T.erase (T.max' hne)).max' hU := by omega
            linarith)
          rw [hmax]
          have hδ : (((T.max' hne - e - (T.erase (T.max' hne)).max' hU : ℕ)) : ℤ) =
              (T.max' hne : ℤ) - e - (T.erase (T.max' hne)).max' hU := by omega
          by_cases h4 : 4 ≤ T.card
          · have hcd := hcond T e hKY h4 hne hU
            have hmin := min_eq_right (show (0 : ℤ) ≤ altSum ((T.erase (T.max' hne)).erase
                ((T.erase (T.max' hne)).max' hU)) -
                ((T.max' hne - e - (T.erase (T.max' hne)).max' hU : ℕ) : ℤ) by rw [hδ]; linarith)
            linarith
          · have h2 : T.card = 2 := by obtain ⟨k, hk⟩ := hev; omega
            have hl := hlast T e hKY h2 hne hU
            have h0' : (T.erase (T.max' hne)).erase ((T.erase (T.max' hne)).max' hU) = ∅ :=
              Finset.card_eq_zero.mp (by omega)
            rw [h0', roundsMargin]
            simp only [Finset.not_nonempty_empty, ↓reduceDIte]
            rw [hδ]
            linarith
    · -- The opponent takes another number; Z takes the largest.
      have hiU : i ∈ T.erase (T.max' hne) := Finset.mem_erase.mpr ⟨hit, hi⟩
      have hmax : (T.erase i).max' hUi = T.max' hne := max'_erase_of_ne hne hit hUi
      have hle : i ≤ T.max' hne := Finset.le_max' T i hi
      have hr : amtReply (T.erase i) e i = T.max' hne := by
        unfold amtReply
        simp only [hUi, ↓reduceDIte, hmax]
        have : ¬ (e + T.max' hne = i ∧ ((T.erase i).erase (T.max' hne)).Nonempty) := by
          rintro ⟨h1, -⟩
          have : i < T.max' hne := lt_of_le_of_ne hle hit
          omega
        simp only [this, ↓reduceDIte]
      rw [hr] at hK1 hK2 hIZ hIY ⊢
      have hc : i ≤ e + T.max' hne := by omega
      simp only [hc, ite_true]
      have h1 := hIY _ (hK1 hc)
      rw [Finset.erase_right_comm] at h1 ⊢
      have hrd := abs_le.mp (altSum_round hne hiU)
      have hcd : (e : ℤ) - altSum T ≤ ((e + T.max' hne - i : ℕ) : ℤ) -
          altSum ((T.erase (T.max' hne)).erase i) := by
        rw [Nat.cast_sub hc]; push_cast; linarith [hrd.1]
      have hm := max_le_max hcd (le_refl (0 : ℤ))
      linarith

end CatchUp
