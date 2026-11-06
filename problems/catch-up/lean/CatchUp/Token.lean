module

public import CatchUp.Transfer
public import Mathlib.Tactic.Ring

/-!
# Token lemma

Claims C26–C31. At equal scores, if the opponent cannot win after a pick `t`, it does not lose
after any other pick `y`: it takes `t` and reaches the node the game after `t` reaches when `y` is
taken, with the same scores (`level_option_ne_loss`). Hence a pick leaving the opponent drawing
makes the level mover draw (`level_law`; `token_lemma` for the smallest number), and so do two
picks each leaving the opponent unable to win (`two_token`). With `t = 1` the conjecture follows
from draws on `{2..N}` at deficit 1 (`conjecture_of_height_two`), or on `{1..N}` for `N ≡ 0 mod 4`
and on `{2..N}` at deficit 1 for `N ≡ 3 mod 4` (`conjecture_of_two_families`); with two tokens,
from one-sided statements (`conjecture_of_leader_pair`, `conjecture_of_suffix_pair`).
-/

@[expose] public section

namespace CatchUp

/-- The outcome of picking `x ∈ R` is in `valueAux_step`'s list. -/
theorem pick_mem_step {R : Finset ℕ} {sm so x : ℕ} (hx : x ∈ R) :
    (if sm + x ≥ so then (valueAux (R.erase x) so (sm + x) false).neg
      else valueAux (R.erase x) (sm + x) so false) ∈
    (R.attach.toList.map fun y =>
      if sm + y.1 ≥ so then (valueAux (R.erase y.1) so (sm + y.1) false).neg
      else valueAux (R.erase y.1) (sm + y.1) so false) :=
  List.mem_map.mpr ⟨⟨x, hx⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩

/-- The mover loses at once when even every number left keeps it strictly behind. -/
theorem valueAux_early_loss {R : Finset ℕ} {sm so : ℕ} (hl : sm + ∑ x ∈ R, x < so) (b : Bool) :
    valueAux R sm so b = .loss := by
  rw [valueAux]
  by_cases h : R = ∅
  · subst h
    simp only [Finset.sum_empty, add_zero] at hl
    simp [hl, Nat.not_lt.mpr hl.le]
  · simp [h, hl]

/-- At equal scores a non-opening turn is one pick, like the opening. -/
theorem valueAux_true_eq_false (R : Finset ℕ) (s : ℕ) :
    valueAux R s s true = valueAux R s s false := by
  rw [valueAux, valueAux]
  simp only [↓reduceIte, Bool.false_eq_true, ge_iff_le, Nat.le_add_right]

/-- **C30, copying step.** At equal scores, for picks `y ≠ t`: if the opponent cannot win after
`t`, it does not lose after `y` (it takes `t` and reaches the node of the game after `t` in which
`y` was taken, with the same scores). -/
theorem level_option_ne_loss {R : Finset ℕ} {t y s : ℕ} (ht : t ∈ R) (hy : y ∈ R) (hyt : y ≠ t)
    (hnw : valueAux (R.erase t) s (s + t) false ≠ .win) :
    valueAux (R.erase y) s (s + y) false ≠ .loss := by
  have hyR' : y ∈ R.erase t := Finset.mem_erase.mpr ⟨hyt, hy⟩
  have htR' : t ∈ R.erase y := Finset.mem_erase.mpr ⟨Ne.symm hyt, ht⟩
  have hcomm : (R.erase t).erase y = (R.erase y).erase t := Finset.erase_right_comm
  have hsy : ∑ z ∈ R.erase y, z = t + ∑ z ∈ (R.erase y).erase t, z :=
    (Finset.add_sum_erase _ _ htR').symm
  have hst : ∑ z ∈ R.erase t, z = y + ∑ z ∈ (R.erase y).erase t, z := by
    rw [← hcomm]; exact (Finset.add_sum_erase _ _ hyR').symm
  have hRy : R.erase y ≠ ∅ := Finset.ne_empty_of_mem htR'
  have hRt : R.erase t ≠ ∅ := Finset.ne_empty_of_mem hyR'
  by_cases hlt : s + ∑ z ∈ R.erase t, z < s + t
  · -- The hypothesis node is an early loss: then y < t, and after the opponent's t the level
    -- mover cannot catch up either.
    have hly : ¬ s + ∑ z ∈ R.erase y, z < s + y := by omega
    rw [valueAux_step hRy hly]
    refine Outcome.best_ne_loss (pick_mem_step (sm := s) (so := s + y) htR') ?_
    rw [ite_eq_left (show s + t ≥ s + y by omega), Outcome.neg_ne_loss]
    have hl2 : s + y + ∑ z ∈ (R.erase y).erase t, z < s + t := by omega
    rw [valueAux_early_loss hl2]
    decide
  · have hlist := hnw
    rw [valueAux_step hRt hlt] at hlist
    have hm := pick_mem_step (sm := s) (so := s + t) hyR'
    rw [hcomm] at hm
    rcases lt_or_gt_of_ne hyt with hlt' | hgt
    · rw [ite_eq_right (show ¬ s + y ≥ s + t by omega)] at hm
      have hP : valueAux ((R.erase y).erase t) (s + y) (s + t) false ≠ .win :=
        fun h => hlist ((Outcome.best_eq_win_iff _).2 (h ▸ hm))
      have hly : ¬ s + ∑ z ∈ R.erase y, z < s + y := by omega
      rw [valueAux_step hRy hly]
      refine Outcome.best_ne_loss (pick_mem_step (sm := s) (so := s + y) htR') ?_
      rw [ite_eq_left (show s + t ≥ s + y by omega)]
      exact Outcome.neg_ne_loss.mpr hP
    · rw [ite_eq_left (show s + y ≥ s + t by omega)] at hm
      have hQ : valueAux ((R.erase y).erase t) (s + t) (s + y) false ≠ .loss := by
        intro hQl
        rw [hQl] at hm
        exact hlist ((Outcome.best_eq_win_iff _).2 hm)
      have hly : ¬ s + ∑ z ∈ R.erase y, z < s + y := by
        intro hl
        exact hQ (valueAux_early_loss (by omega) false)
      rw [valueAux_step hRy hly]
      refine Outcome.best_ne_loss (pick_mem_step (sm := s) (so := s + y) htR') ?_
      rw [ite_eq_right (show ¬ s + t ≥ s + y by omega)]
      exact hQ

/-- **C28, level law.** At equal scores, if some pick `t` leaves the opponent drawing, the level
mover draws: no pick wins. -/
theorem level_law {R : Finset ℕ} {t s : ℕ} (ht : t ∈ R)
    (hd : valueAux (R.erase t) s (s + t) false = .draw) :
    valueAux R s s false = .draw := by
  have hR : R ≠ ∅ := Finset.ne_empty_of_mem ht
  rw [valueAux_step hR (by omega), Outcome.best_eq_draw_iff]
  refine ⟨?_, ?_⟩
  · have h := pick_mem_step (sm := s) (so := s) ht
    rw [ite_eq_left (show s + t ≥ s by omega), hd] at h
    exact h
  · intro hw
    obtain ⟨⟨y, hy⟩, -, hyo⟩ := List.mem_map.mp hw
    rw [ite_eq_left (show s + y ≥ s by omega)] at hyo
    by_cases hyt : y = t
    · subst hyt
      rw [hd] at hyo
      exact absurd hyo (by decide)
    exact Outcome.neg_ne_win.mpr (level_option_ne_loss ht hy hyt (by rw [hd]; decide)) hyo

/-- **C26, token lemma.** The level law with `t` the smallest number left. -/
theorem token_lemma {R : Finset ℕ} {t s : ℕ} (ht : t ∈ R) (_hmin : ∀ x ∈ R, t ≤ x)
    (hd : valueAux (R.erase t) s (s + t) false = .draw) :
    valueAux R s s false = .draw :=
  level_law ht hd

/-- `1 + ⋯ + N` is even exactly when `N ≡ 0` or `3 (mod 4)`. -/
theorem even_triangle_iff (N : ℕ) : Even (N * (N + 1) / 2) ↔ N % 4 = 0 ∨ N % 4 = 3 := by
  rw [Nat.even_iff]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ N = 4 * q + r :=
    ⟨N / 4, N % 4, Nat.mod_lt _ (by decide), (Nat.div_add_mod N 4).symm⟩
  have key : (4 * q + r) * (4 * q + r + 1) = 4 * (4 * q * q + 2 * q * r + q) + r * (r + 1) := by
    ring
  rw [key]
  generalize 4 * q * q + 2 * q * r + q = X
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> omega

/-- **C27.** The conjecture follows from draws on `{1..N}` for `N ≡ 0 (mod 4)` and on `{2..N}`
at deficit 1 for `N ≡ 3 (mod 4)` (scores read at 0). -/
theorem conjecture_of_two_families
    (h0 : ∀ N, N % 4 = 0 → valueAux (Finset.Icc 1 N) 0 0 false = .draw)
    (h3 : ∀ N, N % 4 = 3 → valueAux (Finset.Icc 2 N) 0 1 false = .draw) : Goal := by
  intro N hN
  rw [value, valueAux_true_eq_false]
  rcases (even_triangle_iff N).1 hN with h | h
  · exact h0 N h
  · have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    refine token_lemma h1 (fun x hx => (Finset.mem_Icc.mp hx).1) ?_
    have he : (Finset.Icc 1 N).erase 1 = Finset.Icc 2 N := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [he]
    simpa using h3 N h

/-- **C29.** The conjecture follows from draws on `{2..N}` at deficit 1 for every `N ≥ 2`
with `1 + ⋯ + N` even. -/
theorem conjecture_of_height_two
    (h : ∀ N, 2 ≤ N → Even (N * (N + 1) / 2) → valueAux (Finset.Icc 2 N) 0 1 false = .draw) :
    Goal := by
  intro N hN
  rw [value, valueAux_true_eq_false]
  rcases Nat.lt_or_ge N 2 with hlt | hge
  · -- N = 0: no numbers; N = 1: odd total.
    rcases (by omega : N = 0 ∨ N = 1) with rfl | rfl
    · rw [valueAux]
      simp
    · exact absurd hN (by decide)
  · have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    refine token_lemma h1 (fun x hx => (Finset.mem_Icc.mp hx).1) ?_
    have he : (Finset.Icc 1 N).erase 1 = Finset.Icc 2 N := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [he]
    simpa using h N hge hN

/-- **C30, two-token lemma.** At equal scores, two distinct picks after each of which the opponent
cannot win make the position a draw. -/
theorem two_token {R : Finset ℕ} {t t' s : ℕ} (ht : t ∈ R) (ht' : t' ∈ R) (htt : t ≠ t')
    (h1 : valueAux (R.erase t) s (s + t) false ≠ .win)
    (h2 : valueAux (R.erase t') s (s + t') false ≠ .win) :
    valueAux R s s false = .draw := by
  have hR : R ≠ ∅ := Finset.ne_empty_of_mem ht
  have hnw : ∀ y ∈ R, (valueAux (R.erase y) s (s + y) false).neg ≠ .win := by
    intro y hy
    rw [Outcome.neg_ne_win]
    by_cases hyt : y = t
    · have hyt' : y ≠ t' := by rw [hyt]; exact htt
      exact level_option_ne_loss ht' hy hyt' h2
    · exact level_option_ne_loss ht hy hyt h1
  rw [valueAux_step hR (by omega), Outcome.best_eq_draw_iff]
  refine ⟨?_, ?_⟩
  · have h := pick_mem_step (sm := s) (so := s) ht
    rw [ite_eq_left (show s + t ≥ s by omega)] at h
    have hne1 : (valueAux (R.erase t) s (s + t) false).neg ≠ .loss := Outcome.neg_ne_loss.mpr h1
    have hne2 := hnw t ht
    have hd : (valueAux (R.erase t) s (s + t) false).neg = .draw := by
      revert hne1 hne2
      cases (valueAux (R.erase t) s (s + t) false).neg <;> simp
    rw [hd] at h
    exact h
  · intro hw
    obtain ⟨⟨y, hy⟩, -, hyo⟩ := List.mem_map.mp hw
    rw [ite_eq_left (show s + y ≥ s by omega)] at hyo
    exact hnw y hy hyo

theorem best_of_forall_eq {os : List Outcome} {o : Outcome} (hmem : o ∈ os)
    (hall : ∀ o' ∈ os, o' = o) : Outcome.best os = o := by
  cases o with
  | win => exact (Outcome.best_eq_win_iff os).2 hmem
  | draw => exact (Outcome.best_eq_draw_iff os).2 ⟨hmem, fun h => absurd (hall _ h) (by decide)⟩
  | loss =>
    exact (Outcome.best_eq_loss_iff os).2
      ⟨fun h => absurd (hall _ h) (by decide), fun h => absurd (hall _ h) (by decide)⟩

theorem valueAux_empty (a b : ℕ) (f : Bool) :
    valueAux ∅ a b f = if a > b then .win else if b > a then .loss else .draw := by
  rw [valueAux]; simp

/-- A single number `x` with the mover behind by at most `x`: the mover takes it. -/
theorem valueAux_single {x a b : ℕ} (hab : b ≤ a + x) :
    valueAux {x} a b false = (valueAux ∅ b (a + x) false).neg := by
  have hR : ({x} : Finset ℕ) ≠ ∅ := Finset.singleton_ne_empty x
  have hl : ¬ a + ∑ z ∈ ({x} : Finset ℕ), z < b := by simp; omega
  rw [valueAux_step hR hl]
  apply best_of_forall_eq
  · have h := pick_mem_step (sm := a) (so := b) (Finset.mem_singleton_self x)
    rwa [ite_eq_left (show a + x ≥ b by omega), Finset.erase_singleton] at h
  · intro o' ho'
    obtain ⟨⟨y, hy⟩, -, rfl⟩ := List.mem_map.mp ho'
    have hyx : y = x := Finset.mem_singleton.mp hy
    subst hyx
    dsimp only
    rw [ite_eq_left (show a + y ≥ b by omega), Finset.erase_singleton]

theorem valueAux_two_three : valueAux ({2, 3} : Finset ℕ) 0 1 false ≠ .win := by
  have hR : ({2, 3} : Finset ℕ) ≠ ∅ := by simp
  rw [valueAux_step hR (by simp)]
  refine Outcome.best_ne_win ?_
  intro o ho
  obtain ⟨⟨y, hy⟩, -, rfl⟩ := List.mem_map.mp ho
  dsimp only
  have hy' : y = 2 ∨ y = 3 := by simpa using hy
  rcases hy' with rfl | rfl
  · rw [ite_eq_left (by omega), Outcome.neg_ne_win,
      show ({2, 3} : Finset ℕ).erase 2 = {3} by decide,
      valueAux_single (by omega), valueAux_empty]
    decide
  · rw [ite_eq_left (by omega), Outcome.neg_ne_win,
      show ({2, 3} : Finset ℕ).erase 3 = {2} by decide,
      valueAux_single (by omega), valueAux_empty]
    decide

theorem valueAux_one_two : valueAux ({1, 2} : Finset ℕ) 0 3 false ≠ .win := by
  have hR : ({1, 2} : Finset ℕ) ≠ ∅ := by simp
  rw [valueAux_step hR (by simp)]
  refine Outcome.best_ne_win ?_
  intro o ho
  obtain ⟨⟨y, hy⟩, -, rfl⟩ := List.mem_map.mp ho
  dsimp only
  have hy' : y = 1 ∨ y = 2 := by simpa using hy
  rcases hy' with rfl | rfl
  · rw [ite_eq_right (by omega), show ({1, 2} : Finset ℕ).erase 1 = {2} by decide,
      valueAux_single (by omega), valueAux_empty]
    decide
  · rw [ite_eq_right (by omega), show ({1, 2} : Finset ℕ).erase 2 = {1} by decide,
      valueAux_single (by omega), valueAux_empty]
    decide

theorem value_icc_three : value (Finset.Icc 1 3) = .draw := by
  rw [value, valueAux_true_eq_false]
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 3 := by decide
  have h3 : (3 : ℕ) ∈ Finset.Icc 1 3 := by decide
  refine two_token (s := 0) h1 h3 (by decide) ?_ ?_
  · rw [show (Finset.Icc 1 3).erase 1 = ({2, 3} : Finset ℕ) by decide]
    simpa using valueAux_two_three
  · rw [show (Finset.Icc 1 3).erase 3 = ({1, 2} : Finset ℕ) by decide]
    simpa using valueAux_one_two

/-- The conjecture for N at most 3. -/
theorem conjecture_le_three (N : ℕ) (hN3 : N ≤ 3) (hN : Even (N * (N + 1) / 2)) :
    value (Finset.Icc 1 N) = .draw := by
  rcases (by omega : N = 0 ∨ N = 1 ∨ N = 2 ∨ N = 3) with rfl | rfl | rfl | rfl
  · rw [value, valueAux]; simp
  · exact absurd hN (by decide)
  · exact absurd hN (by decide)
  · exact value_icc_three

theorem Outcome.eq_draw_of_ne {o : Outcome} (hw : o ≠ .win) (hl : o ≠ .loss) : o = .draw := by
  cases o <;> simp_all

/-- **Leader pair.** The conjecture follows from: for every N ≥ 4 with even total, after player 1
opens with 1, and after it opens with 2, player 2 cannot win. -/
theorem conjecture_of_leader_pair
    (h : ∀ N, 4 ≤ N → Even (N * (N + 1) / 2) →
      valueAux ((Finset.Icc 1 N).erase 1) 0 1 false ≠ .win ∧
      valueAux ((Finset.Icc 1 N).erase 2) 0 2 false ≠ .win) :
    Goal := by
  intro N hN
  rcases Nat.lt_or_ge N 4 with hlt | hge
  · exact conjecture_le_three N (by omega) hN
  · rw [value, valueAux_true_eq_false]
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have h2 : (2 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    obtain ⟨a, b⟩ := h N hge hN
    exact two_token (s := 0) h1 h2 (by decide) (by simpa using a) (by simpa using b)

/-- **Suffix pair.** The conjecture follows from: for every N ≥ 4 with even total, the mover does
not win {2..N} when behind by 1, nor {3..N} when behind by 1 (scores 1 and 2: player 2 answered
the opening 1 with 2). -/
theorem conjecture_of_suffix_pair
    (h : ∀ N, 4 ≤ N → Even (N * (N + 1) / 2) →
      valueAux (Finset.Icc 2 N) 0 1 false ≠ .win ∧ valueAux (Finset.Icc 3 N) 1 2 false ≠ .win) :
    Goal := by
  refine conjecture_of_height_two ?_
  intro N hN2 hN
  rcases Nat.lt_or_ge N 4 with hlt | hge
  · rcases (by omega : N = 2 ∨ N = 3) with rfl | rfl
    · exact absurd hN (by decide)
    · rw [show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide]
      refine Outcome.eq_draw_of_ne valueAux_two_three ?_
      have hR : ({2, 3} : Finset ℕ) ≠ ∅ := by simp
      rw [valueAux_step hR (by simp)]
      refine Outcome.best_ne_loss (pick_mem_step (sm := 0) (so := 1)
        (show (3 : ℕ) ∈ ({2, 3} : Finset ℕ) by decide)) ?_
      rw [ite_eq_left (show 0 + 3 ≥ 1 by omega), show ({2, 3} : Finset ℕ).erase 3 = {2} by decide,
        valueAux_single (by omega), valueAux_empty]
      decide
  · obtain ⟨a, b⟩ := h N hge hN
    refine Outcome.eq_draw_of_ne a ?_
    have h2 : (2 : ℕ) ∈ Finset.Icc 2 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have hR : Finset.Icc 2 N ≠ ∅ := Finset.ne_empty_of_mem h2
    have hsum : ¬ 0 + ∑ z ∈ Finset.Icc 2 N, z < 1 := by
      have := Finset.add_sum_erase (Finset.Icc 2 N) (fun z => z) h2
      omega
    have he : (Finset.Icc 2 N).erase 2 = Finset.Icc 3 N := by
      ext y; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
    rw [valueAux_step hR hsum]
    refine Outcome.best_ne_loss (pick_mem_step (sm := 0) (so := 1) h2) ?_
    rw [ite_eq_left (show 0 + 2 ≥ 1 by omega), he]
    exact Outcome.neg_ne_loss.mpr (by simpa using b)

end CatchUp

