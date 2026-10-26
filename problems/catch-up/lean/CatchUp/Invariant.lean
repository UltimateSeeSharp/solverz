module

public import CatchUp.Token

/-!
# Invariant method

A defender Z never loses if it can keep play inside two classes of positions: `KZ` (Z to move) and
`KY` (the opponent Y to move), with Z having a pick that stays in the classes and every pick of Y
staying in them, and every finished game in them at least level for Z (`valueAux_of_invariant`).
The tool for strategy proofs on arbitrary positions; `valueAux_transfer` is its special case on
translated rounds games.
-/

@[expose] public section

namespace CatchUp

/-- **Invariant method.** `KZ R sZ sY`: Z to move with score `sZ` against `sY`; `KY R sY sZ`: Y to
move. If Z always has a pick staying in the classes (or ending the game level or ahead), and
every pick of Y stays in them (or ends the game with Y not ahead), then Z never loses from `KZ`
and Y never wins from `KY`. -/
theorem valueAux_of_invariant (KZ KY : Finset ℕ → ℕ → ℕ → Prop)
    (hZ : ∀ R sZ sY, KZ R sZ sY →
      (R = ∅ → sY ≤ sZ) ∧
      (R ≠ ∅ → ¬ sZ + ∑ x ∈ R, x < sY ∧ ∃ x ∈ R,
        (sY ≤ sZ + x → KY (R.erase x) sY (sZ + x)) ∧ (sZ + x < sY → KZ (R.erase x) (sZ + x) sY)))
    (hY : ∀ R sY sZ, KY R sY sZ →
      (R = ∅ → sY ≤ sZ) ∧
      (R ≠ ∅ → ¬ sY + ∑ x ∈ R, x < sZ → ∀ x ∈ R,
        (sZ ≤ sY + x → KZ (R.erase x) sZ (sY + x)) ∧ (sY + x < sZ → KY (R.erase x) (sY + x) sZ))) :
    ∀ n, ∀ R : Finset ℕ, R.card = n →
      (∀ sZ sY, KZ R sZ sY → valueAux R sZ sY false ≠ .loss) ∧
      (∀ sY sZ, KY R sY sZ → valueAux R sY sZ false ≠ .win) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R hn
  refine ⟨fun sZ sY hk => ?_, fun sY sZ hk => ?_⟩
  · obtain ⟨hempty, hmove⟩ := hZ R sZ sY hk
    by_cases hR : R = ∅
    · subst hR
      rw [valueAux]
      have := hempty rfl
      simp only [↓reduceIte]
      split_ifs <;> first | decide | omega
    obtain ⟨hnl, x, hx, hcY, hcZ⟩ := hmove hR
    rw [valueAux_step hR hnl]
    have hlt : (R.erase x).card < n := by
      rw [← hn]; exact Finset.card_erase_lt_of_mem hx
    refine Outcome.best_ne_loss (pick_mem_step (sm := sZ) (so := sY) hx) ?_
    by_cases hc : sZ + x ≥ sY
    · rw [ite_eq_left hc]
      exact Outcome.neg_ne_loss.mpr ((ih _ hlt _ rfl).2 _ _ (hcY hc))
    · rw [ite_eq_right hc]
      exact (ih _ hlt _ rfl).1 _ _ (hcZ (by omega))
  · obtain ⟨hempty, hmove⟩ := hY R sY sZ hk
    by_cases hR : R = ∅
    · subst hR
      rw [valueAux]
      have := hempty rfl
      simp only [↓reduceIte]
      split_ifs <;> first | decide | omega
    by_cases hel : sY + ∑ x ∈ R, x < sZ
    · rw [valueAux_early_loss hel]
      decide
    rw [valueAux_step hR hel]
    refine Outcome.best_ne_win fun o ho => ?_
    obtain ⟨⟨x, hx⟩, -, rfl⟩ := List.mem_map.mp ho
    have hlt : (R.erase x).card < n := by
      rw [← hn]; exact Finset.card_erase_lt_of_mem hx
    obtain ⟨hcZ, hcY⟩ := hmove hR hel x hx
    by_cases hc : sY + x ≥ sZ
    · simp only [ge_iff_le, hc, ↓reduceIte]
      exact Outcome.neg_ne_win.mpr ((ih _ hlt _ rfl).1 _ _ (hcZ hc))
    · simp only [ge_iff_le, hc, ↓reduceIte]
      exact (ih _ hlt _ rfl).2 _ _ (hcY (by omega))

end CatchUp
