module

public import CatchUp.Rounds

/-!
# Strategy transfer

Claim C22. On offsets placed high, `{a + o : o ∈ T}`, a strategy for Z in the rounds game
carries over to the real game along its own plays, as long as every round start it allows has
offsets at most `a` and a debt that any single pick of the mover covers (`d ≤ a + o` for every
offset `o` left). The strategy is given as two classes of round starts closed under its rounds:
`KZ T d` (Z moves, trailing by `d`) and `KY T e` (the opponent moves, trailing by `e`). Then Z never
loses from a `KZ` state and the opponent never wins from a `KY` state (`valueAux_transfer`).
-/

@[expose] public section

namespace CatchUp

theorem Outcome.best_ne_win {os : List Outcome} (h : ∀ o ∈ os, o ≠ .win) :
    Outcome.best os ≠ .win :=
  fun hb => h _ ((Outcome.best_eq_win_iff os).1 hb) rfl

theorem Outcome.best_ne_loss {os : List Outcome} {o : Outcome} (ho : o ∈ os) (h : o ≠ .loss) :
    Outcome.best os ≠ .loss := by
  intro hb
  obtain ⟨hw, hd⟩ := (Outcome.best_eq_loss_iff os).1 hb
  cases o <;> simp_all

theorem Outcome.neg_ne_loss {o : Outcome} : o.neg ≠ .loss ↔ o ≠ .win := by
  cases o <;> simp [Outcome.neg]

theorem Outcome.neg_ne_win {o : Outcome} : o.neg ≠ .win ↔ o ≠ .loss := by
  cases o <;> simp [Outcome.neg]

theorem sum_map_add_left (T : Finset ℕ) (a : ℕ) :
    ∑ x ∈ T.map (addLeftEmbedding a), x = T.card * a + ∑ o ∈ T, o := by
  rw [Finset.sum_map]
  simp only [addLeftEmbedding_apply]
  rw [Finset.sum_add_distrib, Finset.sum_const]
  rfl

theorem map_erase_add_left (T : Finset ℕ) (a i : ℕ) :
    (T.map (addLeftEmbedding a)).erase (a + i) = (T.erase i).map (addLeftEmbedding a) := by
  rw [Finset.map_erase]; rfl

/-- `valueAux` outside the opening, with numbers left and no early loss: the best pick. -/
theorem valueAux_step {R : Finset ℕ} (h : R ≠ ∅) {sm so : ℕ} (hl : ¬ sm + ∑ x ∈ R, x < so) :
    valueAux R sm so false = Outcome.best (R.attach.toList.map fun x =>
      if sm + x.1 ≥ so then (valueAux (R.erase x.1) so (sm + x.1) false).neg
      else valueAux (R.erase x.1) (sm + x.1) so false) := by
  rw [valueAux]
  simp only [h, hl, ite_false, Bool.false_eq_true]

/-- Every element of the list of outcomes of `valueAux_step` on translated offsets. -/
theorem mem_step_list {T : Finset ℕ} {a sm so : ℕ} {o : Outcome}
    (ho : o ∈ ((T.map (addLeftEmbedding a)).attach.toList.map fun x =>
      if sm + x.1 ≥ so then
        (valueAux ((T.map (addLeftEmbedding a)).erase x.1) so (sm + x.1) false).neg
      else valueAux ((T.map (addLeftEmbedding a)).erase x.1) (sm + x.1) so false)) :
    ∃ i ∈ T, o = if sm + (a + i) ≥ so then
        (valueAux ((T.erase i).map (addLeftEmbedding a)) so (sm + (a + i)) false).neg
      else valueAux ((T.erase i).map (addLeftEmbedding a)) (sm + (a + i)) so false := by
  obtain ⟨⟨x, hx⟩, -, rfl⟩ := List.mem_map.mp ho
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
  exact ⟨i, hi, by simp only [addLeftEmbedding_apply, map_erase_add_left]⟩

/-- The outcome of the pick `a + i` is in the list of `valueAux_step` on translated offsets. -/
theorem step_mem_list {T : Finset ℕ} {a sm so i : ℕ} (hi : i ∈ T) :
    (if sm + (a + i) ≥ so then
        (valueAux ((T.erase i).map (addLeftEmbedding a)) so (sm + (a + i)) false).neg
      else valueAux ((T.erase i).map (addLeftEmbedding a)) (sm + (a + i)) so false) ∈
    ((T.map (addLeftEmbedding a)).attach.toList.map fun x =>
      if sm + x.1 ≥ so then
        (valueAux ((T.map (addLeftEmbedding a)).erase x.1) so (sm + x.1) false).neg
      else valueAux ((T.map (addLeftEmbedding a)).erase x.1) (sm + x.1) so false) := by
  refine List.mem_map.mpr ⟨⟨a + i, Finset.mem_map_of_mem _ hi⟩, Finset.mem_toList.mpr
    (Finset.mem_attach _ _), ?_⟩
  simp only [map_erase_add_left]

/-- **C22.** A Z-strategy in the rounds game, given by classes closed under its rounds, transfers
to the real game on translated offsets: Z never loses from `KZ`, the opponent never wins from
`KY`. -/
theorem valueAux_transfer (a : ℕ) (KZ KY : Finset ℕ → ℕ → Prop)
    (hZa : ∀ T d, KZ T d → ∀ o ∈ T, o ≤ a ∧ d ≤ a + o)
    (hYa : ∀ T e, KY T e → ∀ o ∈ T, o ≤ a ∧ e ≤ a + o)
    (hendZ : ∀ d, KZ ∅ d → d = 0)
    (hZ : ∀ T d, KZ T d → T.Nonempty → ∃ i ∈ T, ∀ j ∈ T.erase i,
      (i ≤ d + j → KZ ((T.erase i).erase j) (d + j - i)) ∧
      (¬ i ≤ d + j → KY ((T.erase i).erase j) (i - d - j)))
    (hY : ∀ T e, KY T e → ∀ i ∈ T, ∃ j ∈ T.erase i,
      (i ≤ e + j → KY ((T.erase i).erase j) (e + j - i)) ∧
      (¬ i ≤ e + j → KZ ((T.erase i).erase j) (i - e - j)))
    (n : ℕ) : ∀ T : Finset ℕ, T.card = n →
      (∀ d, KZ T d → ∀ s, valueAux (T.map (addLeftEmbedding a)) s (s + d) false ≠ .loss) ∧
      (∀ e, KY T e → ∀ s, valueAux (T.map (addLeftEmbedding a)) s (s + e) false ≠ .win) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn
  subst hn
  have ih2 : ∀ i ∈ T, ∀ j ∈ T.erase i,
      (∀ d, KZ ((T.erase i).erase j) d → ∀ s,
        valueAux (((T.erase i).erase j).map (addLeftEmbedding a)) s (s + d) false ≠ .loss) ∧
      (∀ e, KY ((T.erase i).erase j) e → ∀ s,
        valueAux (((T.erase i).erase j).map (addLeftEmbedding a)) s (s + e) false ≠ .win) :=
    fun i hi j hj => ih _ (lt_trans (Finset.card_erase_lt_of_mem hj)
      (Finset.card_erase_lt_of_mem hi)) _ rfl
  by_cases h0 : T = ∅
  · subst h0
    refine ⟨fun d hd s => ?_, fun e _ s => ?_⟩
    · rw [hendZ d hd, valueAux]; simp
    · rw [valueAux]
      simp only [Finset.map_empty, ite_true]
      split_ifs <;> first | omega | simp
  have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
  have hne' : T.map (addLeftEmbedding a) ≠ ∅ := fun h => h0 (Finset.map_eq_empty.mp h)
  -- No early loss at a round start: one pick covers the debt.
  have hnl : ∀ d, (∀ o ∈ T, d ≤ a + o) → ∀ s,
      ¬ s + ∑ x ∈ T.map (addLeftEmbedding a), x < s + d := by
    intro d hd s
    obtain ⟨o, ho⟩ := hne
    have h1 := hd o ho
    have h2 : o ≤ ∑ x ∈ T, x := by have := Finset.sum_erase_add T (fun x => x) ho; omega
    have h3 : a ≤ T.card * a := Nat.le_mul_of_pos_left a (Finset.card_pos.mpr ⟨o, ho⟩)
    rw [sum_map_add_left]
    omega
  constructor
  · -- Z moves: it picks `a + i`, which ends its turn; then every answer is fine for Z.
    intro d hKZ s
    obtain ⟨i, hi, hstep⟩ := hZ T d hKZ hne
    have hia := hZa T d hKZ i hi
    rw [valueAux_step hne' (hnl d (fun o ho => (hZa T d hKZ o ho).2) s)]
    refine Outcome.best_ne_loss (step_mem_list hi) ?_
    have hge : s + (a + i) ≥ s + d := by omega
    simp only [hge, ite_true]
    rw [Outcome.neg_ne_loss]
    -- The opponent's node, trailing by `a + i - d`.
    by_cases h1 : T.erase i = ∅
    · rw [h1, Finset.map_empty, valueAux]
      simp only [ite_true]
      split_ifs <;> first | omega | simp
    by_cases hl : s + d + ∑ x ∈ (T.erase i).map (addLeftEmbedding a), x < s + (a + i)
    · rw [valueAux]
      have h1' : (T.erase i).map (addLeftEmbedding a) ≠ ∅ := fun h => h1 (Finset.map_eq_empty.mp h)
      simp only [h1', hl, ite_false, ite_true]
      simp
    rw [valueAux_step (fun h => h1 (Finset.map_eq_empty.mp h)) hl]
    apply Outcome.best_ne_win
    intro o ho
    obtain ⟨j, hj, rfl⟩ := mem_step_list ho
    obtain ⟨hK1, hK2⟩ := hstep j hj
    by_cases hc : i ≤ d + j
    · have hge' : s + d + (a + j) ≥ s + (a + i) := by omega
      simp only [hge', ite_true]
      rw [Outcome.neg_ne_win, show s + d + (a + j) = s + (a + i) + (d + j - i) by omega]
      exact (ih2 i hi j hj).1 _ (hK1 hc) _
    · have hge' : ¬ s + d + (a + j) ≥ s + (a + i) := by omega
      simp only [hge', ite_false]
      rw [show s + (a + i) = s + d + (a + j) + (i - d - j) by omega]
      exact (ih2 i hi j hj).2 _ (hK2 hc) _
  · -- The opponent moves: each pick `a + i` ends its turn, and Z has an answer.
    intro e hKY s
    rw [valueAux_step hne' (hnl e (fun o ho => (hYa T e hKY o ho).2) s)]
    apply Outcome.best_ne_win
    intro o ho
    obtain ⟨i, hi, rfl⟩ := mem_step_list ho
    have hia := hYa T e hKY i hi
    have hge : s + (a + i) ≥ s + e := by omega
    simp only [hge, ite_true]
    rw [Outcome.neg_ne_win]
    obtain ⟨j, hj, hK1, hK2⟩ := hY T e hKY i hi
    have h1 : T.erase i ≠ ∅ := Finset.ne_empty_of_mem hj
    have h1' : (T.erase i).map (addLeftEmbedding a) ≠ ∅ := fun h => h1 (Finset.map_eq_empty.mp h)
    -- Z is never caught by the early-loss rule: its answer either catches up, or more is left.
    have hl : ¬ s + e + ∑ x ∈ (T.erase i).map (addLeftEmbedding a), x < s + (a + i) := by
      rw [sum_map_add_left]
      have hj2 : j ≤ ∑ x ∈ T.erase i, x := by
        have := Finset.sum_erase_add (T.erase i) (fun x => x) hj; omega
      have hc1 : a ≤ (T.erase i).card * a :=
        Nat.le_mul_of_pos_left a (Finset.card_pos.mpr ⟨j, hj⟩)
      by_cases hc : i ≤ e + j
      · omega
      · have hK := hK2 hc
        have hne2 : (T.erase i).erase j ≠ ∅ := by
          intro he
          rw [he] at hK
          have := hendZ _ hK
          omega
        obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne2
        have hcard : 2 ≤ (T.erase i).card := by
          have := Finset.card_erase_add_one hj
          have : 0 < ((T.erase i).erase j).card := Finset.card_pos.mpr ⟨k, hk⟩
          omega
        have hc2 : 2 * a ≤ (T.erase i).card * a := Nat.mul_le_mul_right a hcard
        omega
    rw [valueAux_step h1' hl]
    refine Outcome.best_ne_loss (step_mem_list hj) ?_
    by_cases hc : i ≤ e + j
    · have hge' : s + e + (a + j) ≥ s + (a + i) := by omega
      simp only [hge', ite_true]
      rw [Outcome.neg_ne_loss, show s + e + (a + j) = s + (a + i) + (e + j - i) by omega]
      exact (ih2 i hi j hj).2 _ (hK1 hc) _
    · have hge' : ¬ s + e + (a + j) ≥ s + (a + i) := by omega
      simp only [hge', ite_false]
      rw [show s + (a + i) = s + e + (a + j) + (i - e - j) by omega]
      exact (ih2 i hi j hj).1 _ (hK2 hc) _

end CatchUp
