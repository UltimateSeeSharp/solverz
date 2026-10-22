module

public import CatchUp.Statement

/-!
# The best outcome by membership

Blueprint L6. `Outcome.best` folds a list from `loss`: it is `win` exactly when some outcome is a
win, else `draw` exactly when some outcome is a draw, else `loss`. So it doesn't depend on the
order of the list, which for the moves of `valueAux` (`Finset.attach.toList`) is unspecified.
-/

public section

namespace CatchUp

/-- The step of `Outcome.best`: win if either is a win, else draw if either is a draw. -/
private def combine (acc o : Outcome) : Outcome :=
  if acc = .win ∨ o = .win then .win else if acc = .draw ∨ o = .draw then .draw else .loss

private theorem best_eq_foldl (os : List Outcome) : Outcome.best os = os.foldl combine .loss := by
  unfold Outcome.best
  congr 1
  funext acc o
  cases acc <;> cases o <;> rfl

private theorem foldl_combine_win (os : List Outcome) :
    ∀ acc, os.foldl combine acc = .win ↔ acc = .win ∨ .win ∈ os := by
  induction os with
  | nil => simp
  | cons o os ih => intro acc; rw [List.foldl_cons, ih]; cases acc <;> cases o <;> simp [combine]

private theorem foldl_combine_draw (os : List Outcome) :
    ∀ acc, os.foldl combine acc = .draw ↔ (acc = .draw ∨ .draw ∈ os) ∧ acc ≠ .win ∧ .win ∉ os := by
  induction os with
  | nil => intro acc; cases acc <;> simp
  | cons o os ih => intro acc; rw [List.foldl_cons, ih]; cases acc <;> cases o <;> simp [combine]

theorem Outcome.best_eq_win_iff (os : List Outcome) : Outcome.best os = .win ↔ .win ∈ os := by
  simp [best_eq_foldl, foldl_combine_win]

theorem Outcome.best_eq_draw_iff (os : List Outcome) :
    Outcome.best os = .draw ↔ .draw ∈ os ∧ .win ∉ os := by
  simp [best_eq_foldl, foldl_combine_draw]

theorem Outcome.best_eq_loss_iff (os : List Outcome) :
    Outcome.best os = .loss ↔ .win ∉ os ∧ .draw ∉ os := by
  rw [← not_iff_not]
  have hw := Outcome.best_eq_win_iff os
  have hd := Outcome.best_eq_draw_iff os
  cases h : Outcome.best os <;> simp_all

end CatchUp
