/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ShiftedReplyCycle.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.FirstPairDescentObstruction

/-!
# Shifted winning-reply cycles

The vertices are alternative first picks from a deficit-one position, not successive
positions of a play. Legal winning replies include directed two-cycles. This module
certifies obstructions to local-span acyclicity and the unconditional maximum-companion
exchange. It does not prove or refute full-interval acyclicity or Catch-Up.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.ShiftedReplyCycle

/-- The normalized child of the positive first pick `a` at deficit one. -/
def child (S : Finset ℕ) (a : ℕ) : Position := ⟨S.erase a, a - 1⟩

/-- A legal winning reply, including the requirement that the child is nonterminal. -/
def Edge (S : Finset ℕ) (a b : ℕ) : Prop :=
  a ∈ S ∧ b ∈ S.erase a ∧
    ¬ (⟨child S a, .p1⟩ : GamePosition).IsTerminal ∧
    (child S a).moveOutcome b = .win

/-- A reply cannot reuse the counter removed by the first pick. -/
theorem edge_irrefl (S : Finset ℕ) (a : ℕ) : ¬ Edge S a a := by
  simp [Edge]

private def checkedValue (p : Position) : Outcome :=
  if CatchUpSearch.CanAvoidLossClassifier.check .p1 ⟨p, .p1⟩ then
    if CatchUpSearch.CanAvoidLossClassifier.check .p2 ⟨p, .p1⟩ then .draw else .win
  else .loss

private theorem checked_value_eq (p : Position) : checkedValue p = p.value := by
  have h₁ := (CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff .p1 ⟨p, .p1⟩).trans
    (can_avoid_loss_iff_value .p1 ⟨p, .p1⟩)
  have h₂ := (CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff .p2 ⟨p, .p1⟩).trans
    (can_avoid_loss_iff_value .p2 ⟨p, .p1⟩)
  cases h : p.value <;> simp_all [checkedValue]

private def checkedMove (p : Position) (b : ℕ) : Outcome :=
  if b < p.deficit then checkedValue (p.afterPick b)
  else (checkedValue (p.afterPick b)).neg

private def checkedEdge (S : Finset ℕ) (a b : ℕ) : Bool :=
  decide (a ∈ S) && decide (b ∈ S.erase a) &&
    decide (¬ (⟨child S a, .p1⟩ : GamePosition).IsTerminal) &&
    decide (checkedMove (child S a) b = .win)

private theorem checked_edge_iff (S : Finset ℕ) (a b : ℕ) :
    checkedEdge S a b = true ↔ Edge S a b := by
  simp [checkedEdge, Edge, checkedMove, checked_value_eq, Position.moveOutcome, and_assoc]

/-- The upward adjacent reply leaves deficit two and switches the mover. -/
theorem adjacent_forward (S : Finset ℕ) (a : ℕ) (ha : 1 ≤ a) :
    (child S a).moveOutcome (a + 1) =
      (⟨(S.erase a).erase (a + 1), 2⟩ : Position).value.neg := by
  simp [child, Position.moveOutcome, Position.afterPick,
    show ¬ a + 1 < a - 1 by omega, show a + 1 - (a - 1) = 2 by omega]

/-- The reverse adjacent reply catches exactly, also switches, and leaves deficit zero. -/
theorem adjacent_reverse (S : Finset ℕ) (a : ℕ) :
    (child S (a + 1)).moveOutcome a =
      (⟨(S.erase a).erase (a + 1), 0⟩ : Position).value.neg := by
  simp [child, Position.moveOutcome, Position.afterPick, Finset.erase_right_comm]

/-- Nonadjacent reversal has two different deficits and only one perspective switch. -/
theorem nonadjacent_reversal (S : Finset ℕ) (a b : ℕ) (ha : 1 ≤ a) (hab : a + 1 < b) :
    (child S a).moveOutcome b =
      (⟨(S.erase a).erase b, b - a + 1⟩ : Position).value.neg ∧
    (child S b).moveOutcome a =
      (⟨(S.erase a).erase b, b - a - 1⟩ : Position).value := by
  simp [child, Position.moveOutcome, Position.afterPick,
    show ¬ b < a - 1 by omega, show a < b - 1 by omega,
    show b - (a - 1) = b - a + 1 by omega, show b - 1 - a = b - a - 1 by omega,
    Finset.erase_right_comm]

/-- The eight-counter residual used for the adjacent two-cycle certificate. -/
def obstructionTail : Finset ℕ := {9, 16, 17, 18, 26, 28, 31, 37}

/-- A support with its cycle span `[3,4]` intact but holes outside that span. -/
def obstruction : Finset ℕ := insert 3 (insert 4 obstructionTail)

/-- Both residuals needed for the two opposite adjacent replies lose. -/
theorem obstruction_tail_losses :
    (⟨obstructionTail, 0⟩ : Position).value = .loss ∧
    (⟨obstructionTail, 2⟩ : Position).value = .loss := by
  rw [← checked_value_eq, ← checked_value_eq]
  decide +kernel

/-- The negative control has minimum three, even effective total, and a full cycle span. -/
theorem obstruction_structure :
    3 ∈ obstruction ∧ (∀ x ∈ obstruction, 3 ≤ x) ∧
      Even (1 + obstruction.sum id) ∧ Finset.Icc 3 4 ⊆ obstruction := by
  decide +kernel

/-- A legal directed two-cycle with its entire integer span present. -/
theorem obstruction_two_cycle : Edge obstruction 3 4 ∧ Edge obstruction 4 3 := by
  rw [← checked_edge_iff, ← checked_edge_iff]
  decide +kernel

/-- The local-span counterexample remains in the hypothetical-loss regime. -/
theorem obstruction_root_loss : (⟨obstruction, 1⟩ : Position).value = .loss := by
  rw [← checked_value_eq]
  decide +kernel

/-- Filling the span of two vertices does not exclude a shifted reply two-cycle. -/
theorem no_local_span_two_cycle_exclusion :
    ¬ (∀ S : Finset ℕ, (∀ x ∈ S, 3 ≤ x) → Even (1 + S.sum id) →
      ∀ a b : ℕ, a < b → Finset.Icc a b ⊆ S → ¬ (Edge S a b ∧ Edge S b a)) := by
  intro h
  exact h obstruction obstruction_structure.2.1 obstruction_structure.2.2.1
    3 4 (by omega) obstruction_structure.2.2.2 obstruction_two_cycle

/-- Even conditioning on an actual deficit-one loss does not repair the local-span claim. -/
theorem no_loss_conditioned_local_span_exclusion :
    ¬ (∀ S : Finset ℕ, (∀ x ∈ S, 3 ≤ x) → Even (1 + S.sum id) →
      (⟨S, 1⟩ : Position).value = .loss →
      ∀ a b : ℕ, a < b → Finset.Icc a b ⊆ S → ¬ (Edge S a b ∧ Edge S b a)) := by
  intro h
  exact h obstruction obstruction_structure.2.1 obstruction_structure.2.2.1
    obstruction_root_loss 3 4 (by omega) obstruction_structure.2.2.2 obstruction_two_cycle

/-- A second support leaves an unused intermediate counter inside each exhibited cycle. -/
def interiorObstruction : Finset ℕ := {3, 4, 5, 6, 9, 19, 24, 26, 29, 38}

/-- The second support contains the whole initial block `[3,6]` and has even effective total. -/
theorem interior_structure :
    (∀ x ∈ interiorObstruction, 3 ≤ x) ∧ Even (1 + interiorObstruction.sum id) ∧
      Finset.Icc 3 6 ⊆ interiorObstruction := by
  decide +kernel

/-- The cycle `3 → 5 → 3` cannot be slid through the available intermediate counter four:
the incoming replacement draws, while the outgoing replacement loses. -/
theorem interior_slide_failure :
    Edge interiorObstruction 3 5 ∧ Edge interiorObstruction 5 3 ∧
      (child interiorObstruction 5).moveOutcome 4 = .draw ∧
      (child interiorObstruction 4).moveOutcome 5 = .loss := by
  have h : checkedEdge interiorObstruction 3 5 = true ∧
      checkedEdge interiorObstruction 5 3 = true ∧
      checkedMove (child interiorObstruction 5) 4 = .draw ∧
      checkedMove (child interiorObstruction 4) 5 = .loss := by decide +kernel
  simpa [checked_edge_iff, checkedMove, checked_value_eq, Position.moveOutcome] using h

/-- A full cycle span alone does not justify sliding the minimum vertex one step upward. -/
theorem no_full_span_minimum_slide :
    ¬ (∀ S : Finset ℕ, (∀ x ∈ S, 3 ≤ x) → Even (1 + S.sum id) →
      ∀ a c : ℕ, a + 1 < c → Finset.Icc a c ⊆ S → Edge S c a → Edge S a c →
        Edge S c (a + 1) ∧ Edge S (a + 1) c) := by
  intro h
  have hs : Finset.Icc 3 5 ⊆ interiorObstruction := by decide +kernel
  have he := h interiorObstruction interior_structure.1 interior_structure.2.1
    3 5 (by omega) hs interior_slide_failure.2.1 interior_slide_failure.1
  have hw := he.1.2.2.2
  rw [interior_slide_failure.2.2.1] at hw
  cases hw

/-- The original sparse three-cycle, independently checked as legal shifted edges. -/
theorem sparse_three_cycle :
    Edge FirstPairDescent.sparse 3 14 ∧ Edge FirstPairDescent.sparse 14 7 ∧
      Edge FirstPairDescent.sparse 7 3 := by
  simp only [← checked_edge_iff]
  decide +kernel

/-- Winning edges need not decrease the numerical label, even on an admissible interval. -/
theorem interval_seven_upward_edge : Edge (Finset.Icc 3 7) 4 6 := by
  rw [← checked_edge_iff]
  decide +kernel

/-- The maximum vertex seven has a winning reply at three. -/
theorem interval_seven_max_edge : Edge (Finset.Icc 3 7) 7 3 := by
  rw [← checked_edge_iff]
  decide +kernel

private theorem checked_seven_max_profile :
    ∀ b : {b // b ∈ Finset.Icc 3 7},
      checkedEdge (Finset.Icc 3 7) 7 b = (b.val == 3) := by
  decide +kernel

/-- The maximum vertex has no second winning reply in this intact interval. -/
theorem interval_seven_no_max_companion :
    ¬ ∃ b, b ≠ 3 ∧ Edge (Finset.Icc 3 7) 7 b := by
  rintro ⟨b, hb, he⟩
  have hm := Finset.mem_of_mem_erase he.2.1
  have hc := (checked_edge_iff _ _ _).mpr he
  rw [checked_seven_max_profile ⟨b, hm⟩] at hc
  exact hb (eq_of_beq hc)

/-- A winning normalized position is nonterminal and has a legal winning pick. -/
theorem win_has_move (p : Position) (hw : p.value = .win) :
    ¬ (⟨p,.p1⟩ : GamePosition).IsTerminal ∧
      ∃ b ∈ p.remaining, p.moveOutcome b = .win := by
  have hn : p.remaining ≠ ∅ := by
    intro h
    rw [Position.value.eq_def, ite_eq_left h] at hw
    split_ifs at hw
  have hc : ¬ p.remaining.sum (fun x ↦ x) < p.deficit := by
    intro h
    rw [Position.value.eq_def, ite_eq_right hn, ite_eq_left h] at hw
    cases hw
  refine ⟨(GamePosition.not_is_terminal_iff _).mpr ⟨hn,hc⟩, ?_⟩
  by_contra! h
  have hb : Outcome.best (p.remaining.attach.toList.map
      fun move ↦ p.moveOutcome move.1) ≠ .win := by
    simpa using h
  exact hb ((Position.value_eq_best_move_outcome p hn hc).symm.trans hw)

/-- A deficit-one loss forces a legal outgoing reply at every positive first pick. -/
theorem loss_forces_outgoing (S : Finset ℕ) (hpos : ∀ a ∈ S, 1 ≤ a)
    (hloss : (⟨S, 1⟩ : Position).value = .loss) :
    ∀ a ∈ S, ∃ b, Edge S a b := by
  intro a ha
  have hw := FirstPairDescent.deficit_one_loss_child_win S a ha (hpos a ha) hloss
  obtain ⟨hnt, b, hb, hwin⟩ := win_has_move (child S a) hw
  exact ⟨b, ha, hb, hnt, hwin⟩

/-- A finite nonempty directed relation with an outgoing edge everywhere has a nonempty
closed directed walk. No undirected-graph convention excluding two-cycles is used. -/
theorem finite_outgoing_closed_walk {α : Type} [Finite α] [Nonempty α]
    (r : α → α → Prop) (h : ∀ a, ∃ b, r a b) :
    ∃ a, Relation.TransGen r a a := by
  by_contra! hn
  let q : α → α → Prop := fun a b ↦ Relation.TransGen r b a
  have : Std.Irrefl q := ⟨hn⟩
  have : IsTrans α q := ⟨fun _ _ _ hab hbc ↦ hbc.trans hab⟩
  have wf := Finite.wellFounded_of_trans_of_irrefl q
  obtain ⟨a⟩ := ‹Nonempty α›
  apply wf.induction a
  intro x ih
  obtain ⟨b,hb⟩ := h x
  exact ih b (Relation.TransGen.single hb)

/-- A losing positive-counter deficit-one position has a closed walk in its shifted graph. -/
theorem loss_forces_closed_walk (S : Finset ℕ) (hS : S.Nonempty)
    (hpos : ∀ a ∈ S, 1 ≤ a) (hloss : (⟨S, 1⟩ : Position).value = .loss) :
    ∃ a : {a // a ∈ S},
      Relation.TransGen (fun a b : {a // a ∈ S} ↦ Edge S a b) a a := by
  have : Nonempty {a // a ∈ S} := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  apply finite_outgoing_closed_walk
  intro a
  obtain ⟨b, hb⟩ := loss_forces_outgoing S hpos hloss a a.property
  exact ⟨⟨b, Finset.mem_of_mem_erase hb.2.1⟩, hb⟩

/-- The endpoint reduction to a closed directed walk, without any acyclicity assumption. -/
theorem interval_loss_forces_closed_walk (N : ℕ) (hN : 7 ≤ N)
    (hloss : (FirstPairDescent.root N).value = .loss) :
    ∃ a : {a // a ∈ Finset.Icc 3 N},
      Relation.TransGen
        (fun a b : {a // a ∈ Finset.Icc 3 N} ↦ Edge (Finset.Icc 3 N) a b) a a := by
  apply loss_forces_closed_walk _ (Finset.nonempty_Icc.mpr (by omega)) _ hloss
  intro a ha
  have := (Finset.mem_Icc.mp ha).1
  omega

private theorem value_win_of_move (p : Position) (b : ℕ)
    (hn : p.remaining ≠ ∅) (hc : ¬ p.remaining.sum (fun x ↦ x) < p.deficit)
    (hb : b ∈ p.remaining) (hw : p.moveOutcome b = .win) : p.value = .win := by
  by_contra h
  rw [Position.value_eq_best_move_outcome p hn hc] at h
  have hall := (Outcome.best_ne_win_iff _).mp h
  exact hall _ (List.mem_map.mpr ⟨⟨b,hb⟩, by simp, rfl⟩) hw

/-- At the critical intermediate counter `c-1`, both three-pick continuations agree.
This is an identity of raw move outcomes and does not assert either pick's legality. -/
theorem critical_cross (S : Finset ℕ) (a c : ℕ) (hac : a + 1 < c) :
    Position.moveOutcome ⟨(S.erase c).erase a, c - a - 1⟩ (c - 1) =
      Position.moveOutcome ⟨(S.erase c).erase (c - 1), 0⟩ a := by
  simp [Position.moveOutcome, Position.afterPick,
    show ¬ c - 1 < c - a - 1 by omega, show c - 1 - (c - a - 1) = a by omega,
    Finset.erase_right_comm]

/-- A winning critical continuation reverses, rather than preserves, the proposed companion
edge. The tied residual is nonterminal because it still contains `a`. -/
theorem critical_reply_inversion (S : Finset ℕ) (a c : ℕ)
    (ha : a ∈ S) (hac : a + 1 < c)
    (hw : Position.moveOutcome ⟨(S.erase c).erase a, c - a - 1⟩ (c - 1) = .win) :
    (child S c).moveOutcome (c - 1) = .loss := by
  rw [critical_cross S a c hac] at hw
  have hm : a ∈ (S.erase c).erase (c - 1) := by
    simp only [Finset.mem_erase]
    exact ⟨by omega, by omega, ha⟩
  have hn : (S.erase c).erase (c - 1) ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨a, hm⟩
  have hv := value_win_of_move ⟨(S.erase c).erase (c - 1), 0⟩ a hn (by simp) hm hw
  simp [child, Position.moveOutcome, Position.afterPick, hv, Outcome.neg]

/-- The critical inversion occurs on the intact size-seven interval. -/
theorem interval_seven_critical_continuation :
    Position.moveOutcome ⟨{4, 5, 6}, 3⟩ 6 = .win ∧
      (child (Finset.Icc 3 7) 7).moveOutcome 6 = .loss := by
  have h : checkedMove ⟨{4, 5, 6}, 3⟩ 6 = .win ∧
      checkedMove (child (Finset.Icc 3 7) 7) 6 = .loss := by decide +kernel
  simpa [checkedMove, checked_value_eq, Position.moveOutcome] using h

end CatchUp.ShiftedReplyCycle
