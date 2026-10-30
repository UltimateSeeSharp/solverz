module

public import CatchUp.Statement

/-!
# Parity law

Claim C3. Every pick moves a number from the remaining set to one of the two scores, so
`s_me + s_opp + ∑ remaining` never changes, and a draw can only come from an empty set with equal
scores. Hence a drawn position has `s_me + s_opp + ∑ remaining` even, and a drawn game has an even
total.
-/

public section

namespace CatchUp

theorem Outcome.neg_eq_draw_iff {o : Outcome} : o.neg = .draw ↔ o = .draw := by
  cases o <;> simp [Outcome.neg]

/-- A fold whose step yields `draw` only from a `draw` accumulator or element. -/
theorem foldl_eq_draw (step : Outcome → Outcome → Outcome)
    (hstep : ∀ acc o, step acc o = .draw → acc = .draw ∨ o = .draw) :
    ∀ (os : List Outcome) (acc : Outcome),
      os.foldl step acc = .draw → acc = .draw ∨ .draw ∈ os := by
  intro os
  induction os with
  | nil => exact fun _ h => Or.inl h
  | cons o os ih =>
    intro acc h
    rcases ih (step acc o) h with h1 | h1
    · rcases hstep acc o h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (by simp [h2])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

theorem Outcome.draw_mem_of_best_eq_draw {os : List Outcome} (h : Outcome.best os = .draw) :
    .draw ∈ os := by
  unfold Outcome.best at h
  rcases foldl_eq_draw _ (by intro acc o; cases acc <;> cases o <;> simp) os .loss h with h1 | h1
  · cases h1
  · exact h1

private theorem parity_law_card (n : ℕ) : ∀ (R : Finset ℕ), R.card = n →
    ∀ (s_me s_opp : ℕ) (isFirstMove : Bool),
      valueAux R s_me s_opp isFirstMove = .draw → Even (s_me + s_opp + R.sum (fun x => x)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hR a b f h
  rw [valueAux] at h
  by_cases h0 : R = ∅
  · -- No numbers left: a draw means equal scores.
    subst h0
    simp only [ite_true] at h
    by_cases hab : a > b
    · simp [hab] at h
    · by_cases hba : b > a
      · simp [hab, hba] at h
      · have : a = b := by omega
        subst this
        simp
  · simp only [h0, ite_false] at h
    by_cases hl : a + R.sum (fun x => x) < b
    · simp [hl] at h -- can't catch up: a loss
    · simp only [hl, ite_false] at h
      -- Some move x ∈ R leads to a drawn position on R.erase x.
      obtain ⟨⟨x, hx⟩, -, hxg⟩ := List.mem_map.mp (Outcome.draw_mem_of_best_eq_draw h)
      have hlt : (R.erase x).card < n := hR ▸ Finset.card_erase_lt_of_mem hx
      have hsum : (R.erase x).sum (fun x => x) + x = R.sum (fun x => x) :=
        Finset.sum_erase_add R _ hx
      simp only at hxg
      cases f with
      | true =>
        simp only [ite_true] at hxg
        have := ih _ hlt (R.erase x) rfl b (a + x) false (Outcome.neg_eq_draw_iff.mp hxg)
        rw [← hsum]; convert this using 1; omega
      | false =>
        simp only [Bool.false_eq_true, ite_false] at hxg
        by_cases hc : a + x ≥ b
        · simp only [hc, ite_true] at hxg
          have := ih _ hlt (R.erase x) rfl b (a + x) false (Outcome.neg_eq_draw_iff.mp hxg)
          rw [← hsum]; convert this using 1; omega
        · simp only [hc, ite_false] at hxg
          have := ih _ hlt (R.erase x) rfl (a + x) b false hxg
          rw [← hsum]; convert this using 1; omega

/-- **Parity law** (C3): in a drawn position the two scores and the numbers left sum to an even
number. -/
theorem parity_law (R : Finset ℕ) (s_me s_opp : ℕ) (isFirstMove : Bool)
    (h : valueAux R s_me s_opp isFirstMove = .draw) : Even (s_me + s_opp + R.sum (fun x => x)) :=
  parity_law_card _ R rfl s_me s_opp isFirstMove h

/-- A drawn game has an even total. -/
theorem even_sum_of_value_eq_draw (S : Finset ℕ) (h : value S = .draw) :
    Even (S.sum fun x => x) := by
  simpa using parity_law S 0 0 true h

end CatchUp
