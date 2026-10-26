module

public import CatchUp.Transfer
public import Mathlib.Tactic.Ring

/-!
# Token lemma

Blueprint L26–L29. At equal scores, if some pick `t` leaves the opponent drawing, the level mover
draws (`level_law`; `token_lemma` is the case of the smallest number). Taking `t` reaches that
position; against any other pick `y` the opponent takes `t` and reaches the node the hypothesis
game reaches after its mover takes `y`, with the same scores. With `t = 1` the conjecture follows
from draws on `{2..N}` at deficit 1 (`conjecture_of_height_two`), or on `{1..N}` for `N ≡ 0 mod 4`
and on `{2..N}` at deficit 1 for `N ≡ 3 mod 4` (`conjecture_of_two_families`).
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

/-- **L28, level law.** At equal scores, if some pick `t` leaves the opponent drawing, the level
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
    have hyR' : y ∈ R.erase t := Finset.mem_erase.mpr ⟨hyt, hy⟩
    have htR' : t ∈ R.erase y := Finset.mem_erase.mpr ⟨Ne.symm hyt, ht⟩
    have hsum : ∑ z ∈ R.erase y, z = t + ∑ z ∈ (R.erase y).erase t, z :=
      (Finset.add_sum_erase _ _ htR').symm
    -- The hypothesis game reaches its option list, and none of its options wins.
    have hRt : R.erase t ≠ ∅ := Finset.ne_empty_of_mem hyR'
    have hlt : ¬ s + ∑ z ∈ R.erase t, z < s + t := by
      intro hl
      rw [valueAux_early_loss hl] at hd
      exact absurd hd (by decide)
    have hlist := hd
    rw [valueAux_step hRt hlt, Outcome.best_eq_draw_iff] at hlist
    have hm := pick_mem_step (sm := s) (so := s + t) hyR'
    rw [Finset.erase_right_comm] at hm
    have hA : valueAux (R.erase y) s (s + y) false ≠ .loss := by
      have hRy : R.erase y ≠ ∅ := Finset.ne_empty_of_mem htR'
      rcases lt_or_gt_of_ne hyt with hlt' | hgt
      · -- y < t: the opponent's t catches up; the mover's node is the hypothesis game's node.
        rw [ite_eq_right (show ¬ s + y ≥ s + t by omega)] at hm
        have hP : valueAux ((R.erase y).erase t) (s + y) (s + t) false ≠ .win :=
          fun h => hlist.2 (h ▸ hm)
        have hly : ¬ s + ∑ z ∈ R.erase y, z < s + y := by omega
        rw [valueAux_step hRy hly]
        refine Outcome.best_ne_loss (pick_mem_step (sm := s) (so := s + y) htR') ?_
        rw [ite_eq_left (show s + t ≥ s + y by omega)]
        exact Outcome.neg_ne_loss.mpr hP
      · -- y > t: the opponent's t keeps it behind; as in the token lemma.
        rw [ite_eq_left (show s + y ≥ s + t by omega)] at hm
        have hQ : valueAux ((R.erase y).erase t) (s + t) (s + y) false ≠ .loss := by
          intro hQl
          rw [hQl] at hm
          exact hlist.2 hm
        have hly : ¬ s + ∑ z ∈ R.erase y, z < s + y := by
          intro hl
          exact hQ (valueAux_early_loss (by omega) false)
        rw [valueAux_step hRy hly]
        refine Outcome.best_ne_loss (pick_mem_step (sm := s) (so := s + y) htR') ?_
        rw [ite_eq_right (show ¬ s + t ≥ s + y by omega)]
        exact hQ
    exact Outcome.neg_ne_win.mpr hA hyo

/-- **L26, token lemma.** The level law with `t` the smallest number left. -/
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

/-- **L27.** The conjecture follows from draws on `{1..N}` for `N ≡ 0 (mod 4)` and on `{2..N}`
at deficit 1 for `N ≡ 3 (mod 4)` (scores read at 0). -/
theorem conjecture_of_two_families
    (h0 : ∀ N, N % 4 = 0 → valueAux (Finset.Icc 1 N) 0 0 false = .draw)
    (h3 : ∀ N, N % 4 = 3 → valueAux (Finset.Icc 2 N) 0 1 false = .draw) : Conjecture := by
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

/-- **L29.** The conjecture follows from draws on `{2..N}` at deficit 1 for every `N ≥ 2`
with `1 + ⋯ + N` even. -/
theorem conjecture_of_height_two
    (h : ∀ N, 2 ≤ N → Even (N * (N + 1) / 2) → valueAux (Finset.Icc 2 N) 0 1 false = .draw) :
    Conjecture := by
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

end CatchUp
