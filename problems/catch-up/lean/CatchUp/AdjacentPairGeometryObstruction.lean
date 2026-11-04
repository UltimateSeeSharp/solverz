/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/AdjacentPairGeometryObstruction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Reference
public import CatchUp.Earlier.TopFourClassification

/-!
# Adjacent-pair reserve obstructions

A smallest leftover counter does not automatically provide a nonwinning reserve.
For every `a ≥ 4`, the support `{a,a+2,a+3}` wins at deficit `a-1`.
For every `a ≥ 6`, opening `a+1` from `([a,a+5],1)` loses: the opponent
chooses `a+5`, after which every repair loses. These are parametric obstructions
to proposed induction rules, not counterexamples to odd-pair nonloss or Catch-Up.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.AdjacentPairGeometry
private theorem close_pair_loss (a b d : ℕ) (ha : 0 < a) (hab : a < b)
    (hgap : b-a < d) (hd : d ≤ a) :
    Position.value ⟨{a,b},d⟩ = .loss := by
  rw [CatchUpSearch.TopFourClassification.value_pair_exact a b d ha hab (by omega)]
  change (if d < b-a then Outcome.win else if d = b-a then Outcome.draw
    else if d ≤ a then Outcome.loss else if d < a+b then Outcome.win
    else if d = a+b then Outcome.draw else Outcome.loss) = .loss
  simp [show ¬ d < b-a by omega, show d ≠ b-a by omega, hd]
private theorem win_of_catching_loss (S : Finset ℕ) (d x : ℕ)
    (hx : x ∈ S) (hdx : d ≤ x)
    (hl : Position.value ⟨S.erase x,x-d⟩ = .loss) :
    Position.value ⟨S,d⟩ = .win := by
  have hsum : x ≤ S.sum id := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  have hn : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨x,hx⟩
  have hc : ¬ S.sum id < d := by omega
  have hm : (⟨S,d⟩ : Position).moveOutcome x = .win := by
    simp [Position.moveOutcome, Position.afterPick, not_lt_of_ge hdx, hl, Outcome.neg]
  by_contra hw
  rw [Position.value_eq_best_move_outcome _ hn hc] at hw
  have hall := (Outcome.best_ne_win_iff _).mp hw
  exact hall .win (List.mem_map.mpr ⟨⟨x,hx⟩, by simp, hm⟩) rfl
/-- A surviving smallest counter need not be a nonwinning reserve for one adjacent pair. -/
theorem orphan_pair_wins (a : ℕ) (ha : 4 ≤ a) :
    Position.value ⟨{a,a+2,a+3},a-1⟩ = .win := by
  apply win_of_catching_loss _ _ (a+3) (by simp) (by omega)
  have he : ({a,a+2,a+3} : Finset ℕ).erase (a+3) = {a,a+2} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [he, show a+3-(a-1)=4 by omega]
  exact close_pair_loss a (a+2) 4 (by omega) (by omega) (by omega) ha

private theorem loss_of_all_catching_children_win (S : Finset ℕ) (d : ℕ)
    (hn : S.Nonempty) (hc : ∀ x ∈ S, d ≤ x)
    (hw : ∀ x ∈ S, Position.value ⟨S.erase x,x-d⟩ = .win) :
    Position.value ⟨S,d⟩ = .loss := by
  obtain ⟨x,hx⟩ := hn
  have hsum : x ≤ S.sum id := Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  have hdx := hc x hx
  have hcatch : ¬ S.sum id < d := by omega
  by_contra hl
  rw [Position.value_eq_best_move_outcome _ (Finset.nonempty_iff_ne_empty.mp ⟨x,hx⟩)
    hcatch] at hl
  obtain ⟨o,ho,hone⟩ := (Outcome.best_ne_loss_iff _).mp hl
  obtain ⟨⟨y,hy⟩,_,rfl⟩ := List.mem_map.mp ho
  apply hone
  simp [Position.moveOutcome, Position.afterPick, not_lt_of_ge (hc y hy),
    hw y hy, Outcome.neg]

/-- After the smallest-upper opening and the largest reply, every repair loses. -/
theorem skipped_quadruple_loses (a : ℕ) (ha : 6 ≤ a) :
    Position.value ⟨{a,a+2,a+3,a+4},5⟩ = .loss := by
  apply loss_of_all_catching_children_win
  · exact ⟨a,by simp⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    omega
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;> subst x
  · have he : ({a,a+2,a+3,a+4} : Finset ℕ).erase a = {a+2,a+3,a+4} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [he]
    apply win_of_catching_loss _ _ (a+2) (by simp) (by omega)
    have hf : ({a+2,a+3,a+4} : Finset ℕ).erase (a+2) = {a+3,a+4} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hf, show a+2-(a-5)=7 by omega]
    exact close_pair_loss (a+3) (a+4) 7 (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+2,a+3,a+4} : Finset ℕ).erase (a+2) = {a,a+3,a+4} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [he, show a+2-5=a-3 by omega]
    apply win_of_catching_loss _ _ a (by simp) (by omega)
    have hf : ({a,a+3,a+4} : Finset ℕ).erase a = {a+3,a+4} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hf, show a-(a-3)=3 by omega]
    exact close_pair_loss (a+3) (a+4) 3 (by omega) (by omega) (by omega) (by omega)
  · have he : ({a,a+2,a+3,a+4} : Finset ℕ).erase (a+3) = {a,a+2,a+4} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [he, show a+3-5=a-2 by omega]
    apply win_of_catching_loss _ _ (a+4) (by simp) (by omega)
    have hf : ({a,a+2,a+4} : Finset ℕ).erase (a+4) = {a,a+2} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hf, show a+4-(a-2)=6 by omega]
    exact close_pair_loss a (a+2) 6 (by omega) (by omega) (by omega) ha
  · have he : ({a,a+2,a+3,a+4} : Finset ℕ).erase (a+4) = {a,a+2,a+3} := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [he, show a+4-5=a-1 by omega]
    exact orphan_pair_wins a (by omega)


/-- The smallest upper counter is a losing move on an interval of three consecutive pairs. -/
theorem smallest_upper_pick_loses (a : ℕ) (ha : 6 ≤ a) :
    (⟨Finset.Icc a (a+5),1⟩ : Position).moveOutcome (a+1) = .loss := by
  have he : (Finset.Icc a (a+5)).erase (a+1) = {a,a+2,a+3,a+4,a+5} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hw : Position.value ⟨{a,a+2,a+3,a+4,a+5},a⟩ = .win := by
    apply win_of_catching_loss _ _ (a+5) (by simp) (by omega)
    have hf : ({a,a+2,a+3,a+4,a+5} : Finset ℕ).erase (a+5) =
        {a,a+2,a+3,a+4} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hf, show a+5-a=5 by omega]
    exact skipped_quadruple_loses a ha
  simpa [Position.moveOutcome, Position.afterPick, he, Outcome.neg] using
    congrArg Outcome.neg hw

/-- The losing proposed opening is available, catches, and starts from a nonterminal state. -/
theorem smallest_upper_pick_legal (a : ℕ) (ha : 6 ≤ a) :
    a+1 ∈ Finset.Icc a (a+5) ∧
    1 ≤ a+1 ∧
    ¬ (⟨⟨Finset.Icc a (a+5),1⟩,.p1⟩ : GamePosition).IsTerminal := by
  have hx : a+1 ∈ Finset.Icc a (a+5) := by simp
  have hs : a+1 ≤ (Finset.Icc a (a+5)).sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  refine ⟨hx, by omega, ?_⟩
  simp only [GamePosition.IsTerminal, not_or]
  constructor
  · exact Finset.nonempty_iff_ne_empty.mp ⟨a+1,hx⟩
  · change ¬ (Finset.Icc a (a+5)).sum id < 1
    omega

end CatchUp.AdjacentPairGeometry
