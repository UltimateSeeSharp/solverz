/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/CompletedMarginBounds.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.TwoBufferProtocol

/-!
# Completed-margin strategy bounds and a necessary transfer condition

A fixed player may enforce a terminal margin inequality against every opponent.
Positive protected lower bounds force a strict win. Any causal two-buffer protocol
is compatible with an actual opponent's upper bound and a shadow protected lower
bound only when the upper bound is at least the lower bound minus two.
The mandatory interval is certified to have exact margin values zero and two.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.TwoBuffer
/-- A fixed player can enforce an arbitrary terminal predicate by legal causal play. -/
def Ensures (player : Player) (accept : GamePosition → Prop) (p : GamePosition) : Prop :=
  if p.IsTerminal then accept p
  else if p.toMove = player then
    ∃ x, ∃ _ : p.LegalMove x, Ensures player accept (p.afterPick x)
  else
    ∀ x, p.LegalMove x → Ensures player accept (p.afterPick x)
termination_by p.remaining.card
decreasing_by
  all_goals exact p.remaining_card_after_pick_lt _ (by assumption)

/-- At a terminal state, an enforceable predicate holds. -/
theorem ensures_terminal (player : Player) (accept : GamePosition → Prop)
    (p : GamePosition) (ht : p.IsTerminal) (h : Ensures player accept p) : accept p := by
  rw [Ensures.eq_def] at h
  simpa only [ite_eq_left ht] using h

/-- A friendly nonterminal state has a legal enforcing continuation. -/
theorem ensures_choice (player : Player) (accept : GamePosition → Prop)
    (p : GamePosition) (ht : ¬p.IsTerminal) (hm : p.toMove = player)
    (h : Ensures player accept p) :
    ∃ x, p.LegalMove x ∧ Ensures player accept (p.afterPick x) := by
  rw [Ensures.eq_def] at h
  simpa only [ite_eq_right ht, ite_eq_left hm, exists_prop] using h

/-- Every legal adversary continuation preserves enforceability. -/
theorem ensures_all (player : Player) (accept : GamePosition → Prop)
    (p : GamePosition) (ht : ¬p.IsTerminal) (hm : p.toMove ≠ player)
    (h : Ensures player accept p) :
    ∀ x, p.LegalMove x → Ensures player accept (p.afterPick x) := by
  rw [Ensures.eq_def] at h
  simpa only [ite_eq_right ht, ite_eq_right hm] using h

/-- Changing the protected player negates the completed margin. -/
theorem completed_margin_neg (p : GamePosition) :
    p.completedMargin .p2 = -p.completedMargin .p1 := by
  simp [GamePosition.completedMargin, Player.scoreCoefficient]

/-- A positive protected margin bound excludes any opponent nonloss strategy. -/
theorem positive_bound_not_avoid (b : ℤ) (hb : 0 < b) (p : GamePosition)
    (hf : Ensures .p1 (fun q ↦ b ≤ q.completedMargin .p1) p) :
    ¬CanAvoidLoss .p2 p := by
  induction p using (measure fun q : GamePosition ↦ q.remaining.card).wf.induction with
  | h p ih =>
    intro ha
    by_cases ht : p.IsTerminal
    · have hf := ensures_terminal _ _ _ ht hf
      have hneg : p.completedMargin .p2 < 0 := by rw [completed_margin_neg]; omega
      exact (can_avoid_loss_iff_terminal_outcome_ne_loss _ _ ht).mp ha
        ((p.completion_sign .p2 ht).2.2.mpr hneg)
    · by_cases hm : p.toMove = .p1
      · obtain ⟨x,hx,hnext⟩ := ensures_choice _ _ _ ht hm hf
        exact ih _ (p.remaining_card_after_pick_lt x hx) hnext
          ((can_avoid_loss_iff_forall_safe_moves _ _ ht (by simp [hm])).mp ha x hx)
      · have hm2 : p.toMove = .p2 := by cases he : p.toMove <;> simp_all
        obtain ⟨x,hx,hnext⟩ :=
          (can_avoid_loss_iff_exists_safe_move _ _ ht hm2).mp ha
        exact ih _ (p.remaining_card_after_pick_lt x hx)
          (ensures_all _ _ _ ht hm hf x hx) hnext

/-- Actual upper and positive shadow lower bounds constrain every causal protocol. -/
theorem protocol_necessary_bound {u v : GamePosition} (h : Protocol u v)
    (a b : ℤ) (hb : 0 < b)
    (hu : Ensures .p2 (fun p ↦ p.completedMargin .p1 ≤ a) u)
    (hv : Ensures .p1 (fun p ↦ b ≤ p.completedMargin .p1) v) : b - 2 ≤ a := by
  induction h with
  | finish buffer tu tv hm =>
    have hU := ensures_terminal _ _ _ tu hu
    have hV := ensures_terminal _ _ _ tv hv
    omega
  | actualPick buffer ht turn x legal next ih =>
    exact ih (ensures_all _ _ _ ht (by simp [turn]) hu x legal) hv
  | actualOpponent buffer ht turn next ih =>
    obtain ⟨x,hx,hnext⟩ := ensures_choice _ _ _ ht turn hu
    exact ih x hx hnext hv
  | shadowPick buffer ht turn x legal next ih =>
    exact ih hu (ensures_all _ _ _ ht (by simp [turn]) hv x legal)
  | shadowStrategy buffer ht turn nonempty next ih =>
    obtain ⟨x,hx,hnext⟩ := ensures_choice _ _ _ ht turn hv
    exact ih x hx (positive_bound_not_avoid b hb _ hnext) hu hnext


/-- Executable bounded-depth verification of a terminal guarantee. -/
def forceCheck (player : Player) (accept : GamePosition → Bool) :
    ℕ → GamePosition → Bool
  | 0, p => decide p.IsTerminal && accept p
  | n+1, p =>
    if p.IsTerminal then accept p
    else if p.toMove = player then
      decide (∃ x ∈ p.remaining, forceCheck player accept n (p.afterPick x) = true)
    else
      decide (∀ x ∈ p.remaining, forceCheck player accept n (p.afterPick x) = true)

/-- Successful guarantee checking constructs the quantified strategy property. -/
theorem force_check_sound (player : Player) (accept : GamePosition → Bool)
    (n : ℕ) (p : GamePosition) (h : forceCheck player accept n p = true) :
    Ensures player (fun q ↦ accept q = true) p := by
  induction n generalizing p with
  | zero =>
    simp only [forceCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [Ensures.eq_def, ite_eq_left h.1]
    exact h.2
  | succ n ih =>
    rw [Ensures.eq_def]
    split_ifs with ht hm
    · simpa only [forceCheck, ite_eq_left ht] using h
    · simp only [forceCheck, ite_eq_right ht, ite_eq_left hm, decide_eq_true_eq] at h
      obtain ⟨x,hx,hn⟩ := h
      exact ⟨x,hx,ih _ hn⟩
    · simp only [forceCheck, ite_eq_right ht, ite_eq_right hm, decide_eq_true_eq] at h
      exact fun x hx ↦ ih _ (h x hx)

/-- Matching lower and upper strategies certify exact margin values zero and two. -/
theorem mandatory_scalar_bounds :
    Ensures .p1 (fun p ↦ (0 : ℤ) ≤ p.completedMargin .p1)
      ⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ ∧
    Ensures .p2 (fun p ↦ p.completedMargin .p1 ≤ (0 : ℤ))
      ⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ ∧
    Ensures .p1 (fun p ↦ (2 : ℤ) ≤ p.completedMargin .p1)
      ⟨AdjacentHoleExchange.exchangeRight,.p1⟩ ∧
    Ensures .p2 (fun p ↦ p.completedMargin .p1 ≤ (2 : ℤ))
      ⟨AdjacentHoleExchange.exchangeRight,.p1⟩ := by
  have huL := force_check_sound .p1 (fun p ↦ decide ((0 : ℤ) ≤ p.completedMargin .p1))
    6 ⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ (by decide +kernel)
  have huU := force_check_sound .p2 (fun p ↦ decide (p.completedMargin .p1 ≤ (0 : ℤ)))
    6 ⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ (by decide +kernel)
  have hvL := force_check_sound .p1 (fun p ↦ decide ((2 : ℤ) ≤ p.completedMargin .p1))
    6 ⟨AdjacentHoleExchange.exchangeRight,.p1⟩ (by decide +kernel)
  have hvU := force_check_sound .p2 (fun p ↦ decide (p.completedMargin .p1 ≤ (2 : ℤ)))
    6 ⟨AdjacentHoleExchange.exchangeRight,.p1⟩ (by decide +kernel)
  simpa only [decide_eq_true_eq] using And.intro huL (And.intro huU (And.intro hvL hvU))
end CatchUp.TwoBuffer
