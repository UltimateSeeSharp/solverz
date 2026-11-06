/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/CompletedTurn.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Reference

/-!
# Completed Catch-Up turns

This module gives both an ordered trace and an exact unordered finite-set characterization of one
completed Catch-Up turn. It permits turn-level arguments to reason about chosen subsets and their
sums while retaining a proof that every pick is a legal game step. It also flattens the primitive
minimax recursion across a whole completed turn, both as traces and as legal subsets.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

open scoped BigOperators

/-- Apply a list of raw picks in order. Legality is recorded separately by `CompletedTurn`. -/
def GamePosition.afterPicks : GamePosition → List ℕ → GamePosition
  | position, [] => position
  | position, x :: xs => (position.afterPick x).afterPicks xs

@[simp]
theorem GamePosition.after_picks_nil (position : GamePosition) :
    position.afterPicks [] = position := rfl

@[simp]
theorem GamePosition.after_picks_cons (position : GamePosition) (x : ℕ) (xs : List ℕ) :
    position.afterPicks (x :: xs) = (position.afterPick x).afterPicks xs := rfl

/--
An ordered trace of exactly one completed post-opening turn.

The `more` constructor records a pick that leaves the mover strictly behind. The `finish`
constructor records the unique final pick, which catches up or ties. Availability is checked at
every pick; nonterminality will follow from completion and is proved below.
-/
inductive CompletedTurn : GamePosition → List ℕ → GamePosition → Prop
  | finish (position : GamePosition) (x : ℕ)
      (legal : position.LegalMove x) (catches : position.deficit ≤ x) :
      CompletedTurn position [x] (position.afterPick x)
  | more (position : GamePosition) (x : ℕ) (xs : List ℕ) (after : GamePosition)
      (legal : position.LegalMove x) (behind : x < position.deficit)
      (tail : CompletedTurn (position.afterPick x) xs after) :
      CompletedTurn position (x :: xs) after

/-- A list-indexed trace of actual nonterminal game steps. -/
inductive GamePosition.PickTrace : GamePosition → List ℕ → GamePosition → Prop
  | nil (position : GamePosition) : PickTrace position [] position
  | cons (position : GamePosition) (x : ℕ) (xs : List ℕ) (after : GamePosition)
      (step : position.Step (position.afterPick x))
      (tail : PickTrace (position.afterPick x) xs after) :
      PickTrace position (x :: xs) after

/-- The unordered data specifying a completed turn and its distinguished final counter. -/
structure TurnSet (before : GamePosition) (chosen : Finset ℕ) (final : ℕ) : Prop where
  final_mem : final ∈ chosen
  chosen_subset : chosen ⊆ before.remaining
  catches : before.deficit ≤ chosen.sum (fun x => x)
  preparation_below :
    chosen = {final} ∨ (chosen.erase final).sum (fun x => x) < before.deficit

/-- The endpoint determined solely by the starting position and unordered chosen set. -/
def completedTurnEndpoint (before : GamePosition) (chosen : Finset ℕ) : GamePosition where
  remaining := before.remaining \ chosen
  deficit := chosen.sum (fun x => x) - before.deficit
  toMove := before.toMove.other

theorem CompletedTurn.picks_nonempty {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) : picks ≠ [] := by
  cases trace <;> simp

theorem CompletedTurn.after_eq_after_picks {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) : after = before.afterPicks picks := by
  induction trace with
  | finish => rfl
  | more position x xs after legal behind tail ih =>
      simpa using ih

theorem CompletedTurn.picks_subset_remaining {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) : picks.toFinset ⊆ before.remaining := by
  induction trace with
  | finish position x legal catches =>
      simpa [GamePosition.LegalMove] using legal
  | more position x xs after legal behind tail ih =>
      intro y hy
      simp only [List.toFinset_cons, Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact legal
      · exact Finset.mem_of_mem_erase (ih hy)

theorem CompletedTurn.picks_nodup {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) : picks.Nodup := by
  induction trace with
  | finish => simp
  | more position x xs after legal behind tail ih =>
      rw [List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hx
      have hxFinset : x ∈ xs.toFinset := by simpa using hx
      have hxErased := tail.picks_subset_remaining hxFinset
      change x ∈ position.remaining.erase x at hxErased
      simp at hxErased

theorem CompletedTurn.total_catches {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) : before.deficit ≤ picks.sum := by
  induction trace with
  | finish position x legal catches => simpa using catches
  | more position x xs after legal behind tail ih =>
      simp only [List.sum_cons]
      simp only [GamePosition.afterPick, Position.afterPick, behind, ite_true] at ih
      omega

theorem CompletedTurn.after_remaining {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) :
    after.remaining = before.remaining \ picks.toFinset := by
  induction trace with
  | finish position x legal catches =>
      ext y
      simp [GamePosition.afterPick, Position.afterPick, and_comm]
  | more position x xs after legal behind tail ih =>
      rw [ih, GamePosition.remaining_after_pick]
      ext y
      simp [and_assoc, and_left_comm]

theorem CompletedTurn.after_deficit {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) :
    after.deficit = picks.sum - before.deficit := by
  induction trace with
  | finish position x legal catches =>
      simp [GamePosition.afterPick, Position.afterPick, not_lt_of_ge catches]
  | more position x xs after legal behind tail ih =>
      simp only [GamePosition.afterPick, Position.afterPick, behind, ite_true] at ih
      simp only [List.sum_cons]
      have htail := tail.total_catches
      simp only [GamePosition.afterPick, Position.afterPick, behind, ite_true] at htail
      omega

theorem CompletedTurn.after_to_move {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) :
    after.toMove = before.toMove.other := by
  induction trace with
  | finish position x legal catches =>
      exact GamePosition.to_move_after_pick_of_le position x catches
  | more position x xs after legal behind tail ih =>
      rw [ih, GamePosition.to_move_after_pick_of_lt position x behind]

theorem CompletedTurn.after_eq_endpoint {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) :
    after = completedTurnEndpoint before picks.toFinset := by
  have hsum := List.sum_toFinset (fun x : ℕ => x) trace.picks_nodup
  have hsum' : picks.toFinset.sum (fun x => x) = picks.sum := by simpa using hsum
  have hremaining := trace.after_remaining
  have hdeficit := trace.after_deficit
  have htoMove := trace.after_to_move
  cases before with
  | mk beforePosition beforeMover =>
      cases beforePosition with
      | mk beforeRemaining beforeDeficit =>
          cases after with
          | mk afterPosition afterMover =>
              cases afterPosition with
              | mk afterRemaining afterDeficit =>
                  try simp only at hremaining hdeficit htoMove
                  simp only [completedTurnEndpoint]
                  rw [hremaining, hdeficit, htoMove, hsum']

theorem CompletedTurn.before_not_terminal {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) : ¬before.IsTerminal := by
  rw [GamePosition.not_is_terminal_iff]
  have hnonempty := trace.picks_nonempty
  have hmemList : picks.head hnonempty ∈ picks := List.head_mem hnonempty
  have hmemFinset : picks.head hnonempty ∈ picks.toFinset := by
    rw [List.mem_toFinset]
    exact hmemList
  have hselected := trace.picks_subset_remaining hmemFinset
  refine ⟨Finset.ne_empty_of_mem hselected, ?_⟩
  have hsumSubset : picks.toFinset.sum (fun x => x) ≤
      before.remaining.sum (fun x => x) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg trace.picks_subset_remaining
    intros
    omega
  have hsum := List.sum_toFinset (fun x : ℕ => x) trace.picks_nodup
  have hsum' : picks.toFinset.sum (fun x => x) = picks.sum := by simpa using hsum
  rw [hsum'] at hsumSubset
  have hcatches := trace.total_catches
  omega

theorem CompletedTurn.first_step {before after : GamePosition} {x : ℕ} {xs : List ℕ}
    (trace : CompletedTurn before (x :: xs) after) :
    before.Step (before.afterPick x) := by
  apply GamePosition.step_after_pick
  · exact trace.before_not_terminal
  · cases trace with
    | finish => assumption
    | more => assumption

/-- Every pick in a completed-turn trace is an actual step from a nonterminal source. -/
theorem CompletedTurn.pick_trace {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after) :
    GamePosition.PickTrace before picks after := by
  induction trace with
  | finish position x legal catches =>
      have turn := CompletedTurn.finish position x legal catches
      exact GamePosition.PickTrace.cons position x [] (position.afterPick x)
        (GamePosition.step_after_pick position x turn.before_not_terminal legal)
        (GamePosition.PickTrace.nil (position.afterPick x))
  | more position x xs after legal behind tail ih =>
      have turn := CompletedTurn.more position x xs after legal behind tail
      exact GamePosition.PickTrace.cons position x xs after
        (GamePosition.step_after_pick position x turn.before_not_terminal legal) ih

theorem completed_turn_cons_iff
    (before after : GamePosition) (x : ℕ) (xs : List ℕ) :
    CompletedTurn before (x :: xs) after ↔
      (xs = [] ∧ before.LegalMove x ∧ before.deficit ≤ x ∧
        after = before.afterPick x) ∨
      (before.LegalMove x ∧ x < before.deficit ∧
        CompletedTurn (before.afterPick x) xs after) := by
  constructor
  · intro trace
    cases trace with
    | finish position y legal catches =>
        exact Or.inl ⟨rfl, legal, catches, rfl⟩
    | more position y ys after legal behind tail =>
        exact Or.inr ⟨legal, behind, tail⟩
  · rintro (⟨rfl, legal, catches, rfl⟩ | ⟨legal, behind, tail⟩)
    · exact CompletedTurn.finish before x legal catches
    · exact CompletedTurn.more before x xs after legal behind tail

theorem CompletedTurn.preparation_sum_lt_or_empty
    {before after : GamePosition} {preparation : List ℕ} {final : ℕ}
    (trace : CompletedTurn before (preparation ++ [final]) after) :
    preparation = [] ∨ preparation.sum < before.deficit := by
  induction preparation generalizing before after with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      right
      have htrace : CompletedTurn before (x :: (xs ++ [final])) after := by
        simpa using trace
      rcases (completed_turn_cons_iff before after x (xs ++ [final])).mp htrace with
        hfinish | ⟨legal, behind, tail⟩
      · simp at hfinish
      · have htail := ih tail
        simp only [List.sum_cons]
        simp only [GamePosition.afterPick, Position.afterPick, behind, ite_true] at htail
        rcases htail with rfl | htail
        · simp only [List.sum_nil, add_zero]
          exact behind
        · omega

theorem completed_turn_of_preparation
    (before : GamePosition) (preparation : List ℕ) (final : ℕ)
    (hnodup : preparation.Nodup) (hfinal : final ∉ preparation)
    (hsubset : insert final preparation.toFinset ⊆ before.remaining)
    (hbelow : preparation = [] ∨ preparation.sum < before.deficit)
    (hcatches : before.deficit ≤ preparation.sum + final) :
    CompletedTurn before (preparation ++ [final])
      (completedTurnEndpoint before (insert final preparation.toFinset)) := by
  induction preparation generalizing before with
  | nil =>
      simp only [List.sum_nil, zero_add] at hcatches
      have hlegal : before.LegalMove final := by
        apply hsubset
        simp
      have trace := CompletedTurn.finish before final hlegal hcatches
      have hendpoint := trace.after_eq_endpoint
      rw [hendpoint] at trace
      simpa using trace
  | cons x xs ih =>
      simp only [List.nodup_cons] at hnodup
      simp only [List.mem_cons, not_or] at hfinal
      simp only [List.cons_ne_nil, false_or, List.sum_cons] at hbelow
      simp only [List.sum_cons] at hcatches
      have hlegal : before.LegalMove x := by
        apply hsubset
        simp
      have hchildSubset :
          insert final xs.toFinset ⊆ (before.afterPick x).remaining := by
        intro y hy
        change y ∈ before.remaining.erase x
        rw [Finset.mem_erase]
        have hxNot : x ∉ insert final xs.toFinset := by
          simp only [Finset.mem_insert, List.mem_toFinset, not_or]
          exact ⟨Ne.symm hfinal.1, hnodup.1⟩
        refine ⟨?_, ?_⟩
        · intro hyx
          subst y
          exact hxNot hy
        · apply hsubset
          simp only [List.toFinset_cons, Finset.mem_insert] at hy ⊢
          tauto
      have hchildBelow :
          xs = [] ∨ xs.sum < (before.afterPick x).deficit := by
        right
        simp only [GamePosition.afterPick, Position.afterPick,
          ite_eq_left (show x < before.deficit by omega)]
        omega
      have hchildCatches :
          (before.afterPick x).deficit ≤ xs.sum + final := by
        simp only [GamePosition.afterPick, Position.afterPick,
          ite_eq_left (show x < before.deficit by omega)]
        omega
      have tail := ih (before.afterPick x) hnodup.2 hfinal.2 hchildSubset hchildBelow
        hchildCatches
      have trace := CompletedTurn.more before x (xs ++ [final])
        (completedTurnEndpoint (before.afterPick x) (insert final xs.toFinset))
        hlegal (by omega) tail
      have hendpoint := trace.after_eq_endpoint
      rw [hendpoint] at trace
      simpa [Finset.insert_comm] using trace

/-- Every ordering of the preparation set, followed by the distinguished final counter, works. -/
theorem TurnSet.completed_turn_of_preparation
    {before : GamePosition} {chosen : Finset ℕ} {final : ℕ}
    (turn : TurnSet before chosen final) (preparation : List ℕ)
    (hnodup : preparation.Nodup)
    (hpreparation : preparation.toFinset = chosen.erase final) :
    CompletedTurn before (preparation ++ [final]) (completedTurnEndpoint before chosen) := by
  have hfinal : final ∉ preparation := by
    intro hmem
    have hmemFinset : final ∈ preparation.toFinset := by simpa using hmem
    rw [hpreparation] at hmemFinset
    simp at hmemFinset
  have hinsert : insert final preparation.toFinset = chosen := by
    rw [hpreparation]
    exact Finset.insert_erase turn.final_mem
  have hsubset : insert final preparation.toFinset ⊆ before.remaining := by
    rw [hinsert]
    exact turn.chosen_subset
  have hsum : preparation.toFinset.sum (fun x => x) = preparation.sum := by
    simpa using List.sum_toFinset (fun x : ℕ => x) hnodup
  have hbelow : preparation = [] ∨ preparation.sum < before.deficit := by
    rcases turn.preparation_below with hsingleton | hstrict
    · left
      have hempty : preparation.toFinset = ∅ := by
        rw [hpreparation, hsingleton]
        simp
      simpa using hempty
    · right
      rw [← hsum, hpreparation]
      exact hstrict
  have hcatches : before.deficit ≤ preparation.sum + final := by
    calc
      before.deficit ≤ chosen.sum (fun x => x) := turn.catches
      _ = (chosen.erase final).sum (fun x => x) + final :=
        (Finset.sum_erase_add chosen (fun x => x) turn.final_mem).symm
      _ = preparation.toFinset.sum (fun x => x) + final := by rw [hpreparation]
      _ = preparation.sum + final := by rw [hsum]
  have trace := CatchUp.completed_turn_of_preparation before preparation final hnodup hfinal hsubset
    hbelow hcatches
  rw [hinsert] at trace
  exact trace

/-- An ordered completed turn yields exactly the corresponding unordered turn-set data. -/
theorem CompletedTurn.turn_set
    {before after : GamePosition} {preparation : List ℕ} {final : ℕ}
    (trace : CompletedTurn before (preparation ++ [final]) after) :
    TurnSet before (insert final preparation.toFinset) final := by
  have hparts : preparation.Nodup ∧ final ∉ preparation := by
    have hparts' : preparation.Nodup ∧ ∀ a ∈ preparation, ¬a = final := by
      simpa [List.nodup_append] using trace.picks_nodup
    refine ⟨hparts'.1, ?_⟩
    intro hfinal
    exact hparts'.2 final hfinal rfl
  have hsum := List.sum_toFinset (fun x : ℕ => x) trace.picks_nodup
  have hsum' : (preparation ++ [final]).toFinset.sum (fun x => x) =
      (preparation ++ [final]).sum := by simpa using hsum
  refine ⟨by simp, ?_, ?_, ?_⟩
  · simpa [Finset.insert_comm] using trace.picks_subset_remaining
  · have hcatches := trace.total_catches
    rw [← hsum'] at hcatches
    simpa [Finset.insert_comm] using hcatches
  · rcases trace.preparation_sum_lt_or_empty with rfl | hstrict
    · exact Or.inl (by simp)
    · right
      have hsumPreparation := List.sum_toFinset (fun x : ℕ => x) hparts.1
      have hsumPreparation' : preparation.toFinset.sum (fun x => x) =
          preparation.sum := by simpa using hsumPreparation
      simpa [hparts.2, hsumPreparation'] using hstrict

/-- Exact equivalence between a completed turn trace and an unordered set with a final counter. -/
theorem exists_completed_turn_iff_turn_set
    (before after : GamePosition) (chosen : Finset ℕ) (final : ℕ) :
    (∃ preparation : List ℕ,
      CompletedTurn before (preparation ++ [final]) after ∧
        (preparation ++ [final]).toFinset = chosen) ↔
      TurnSet before chosen final ∧ after = completedTurnEndpoint before chosen := by
  constructor
  · rintro ⟨preparation, trace, hchosen⟩
    have hchosen' : insert final preparation.toFinset = chosen := by
      simpa [Finset.insert_comm] using hchosen
    have hturn := trace.turn_set
    rw [hchosen'] at hturn
    have hendpoint := trace.after_eq_endpoint
    rw [hchosen] at hendpoint
    exact ⟨hturn, hendpoint⟩
  · rintro ⟨turn, hafter⟩
    let preparation := (chosen.erase final).toList
    have hnodup : preparation.Nodup := by
      exact Finset.nodup_toList (chosen.erase final)
    have hpreparation : preparation.toFinset = chosen.erase final := by
      exact Finset.toList_toFinset (chosen.erase final)
    have trace := turn.completed_turn_of_preparation preparation hnodup hpreparation
    refine ⟨preparation, ?_, ?_⟩
    · rw [hafter]
      exact trace
    · simpa [preparation, Finset.insert_comm] using
        (Finset.insert_erase turn.final_mem)

/-- At positive deficit, a nonempty chosen set can be played as one completed turn exactly when
its total reaches the deficit but remains below the deficit plus its maximum counter. -/
theorem exists_turn_set_iff_sum_lt_deficit_add_max
    (before : GamePosition) (chosen : Finset ℕ) (hdeficit : 0 < before.deficit) :
    (∃ final, TurnSet before chosen final) ↔
      ∃ hchosen : chosen.Nonempty,
        chosen ⊆ before.remaining ∧
          before.deficit ≤ chosen.sum (fun x => x) ∧
            chosen.sum (fun x => x) < before.deficit + chosen.max' hchosen := by
  constructor
  · rintro ⟨final, turn⟩
    let hchosen : chosen.Nonempty := ⟨final, turn.final_mem⟩
    refine ⟨hchosen, turn.chosen_subset, turn.catches, ?_⟩
    have hfinal_le : final ≤ chosen.max' hchosen := chosen.le_max' final turn.final_mem
    rcases turn.preparation_below with hsingleton | hbelow
    · subst chosen
      simp
      omega
    · have hsum : (chosen.erase final).sum (fun x => x) + final =
          chosen.sum (fun x => x) := by
        simpa using Finset.sum_erase_add chosen (fun x => x) turn.final_mem
      omega
  · rintro ⟨hchosen, hsubset, hcatches, hbelow⟩
    let final := chosen.max' hchosen
    have hfinal : final ∈ chosen := by
      simpa [final] using Finset.max'_mem chosen hchosen
    refine ⟨final, ⟨hfinal, hsubset, hcatches, Or.inr ?_⟩⟩
    have hsum : (chosen.erase final).sum (fun x => x) + final =
        chosen.sum (fun x => x) := by
      simpa using Finset.sum_erase_add chosen (fun x => x) hfinal
    simpa [final] using (show (chosen.erase final).sum (fun x => x) < before.deficit by omega)

/-- At positive deficit, the completed turns removing `chosen` are exactly the nonempty subsets
whose total lies in the half-open interval from the deficit to deficit plus their maximum. -/
theorem exists_completed_turn_iff_sum_lt_deficit_add_max
    (before after : GamePosition) (chosen : Finset ℕ) (hdeficit : 0 < before.deficit) :
    (∃ final preparation,
      CompletedTurn before (preparation ++ [final]) after ∧
        (preparation ++ [final]).toFinset = chosen) ↔
      ∃ hchosen : chosen.Nonempty,
        chosen ⊆ before.remaining ∧
          before.deficit ≤ chosen.sum (fun x => x) ∧
            chosen.sum (fun x => x) < before.deficit + chosen.max' hchosen ∧
              after = completedTurnEndpoint before chosen := by
  constructor
  · rintro ⟨final, preparation, trace, hchosen⟩
    have hturnEndpoint :=
      (exists_completed_turn_iff_turn_set before after chosen final).1
        ⟨preparation, trace, hchosen⟩
    have hturnData :=
      (exists_turn_set_iff_sum_lt_deficit_add_max before chosen hdeficit).1
        ⟨final, hturnEndpoint.1⟩
    rcases hturnData with ⟨hne, hsubset, hcatches, hbelow⟩
    exact ⟨hne, hsubset, hcatches, hbelow, hturnEndpoint.2⟩
  · rintro ⟨hne, hsubset, hcatches, hbelow, hafter⟩
    rcases (exists_turn_set_iff_sum_lt_deficit_add_max before chosen hdeficit).2
        ⟨hne, hsubset, hcatches, hbelow⟩ with ⟨final, turn⟩
    rcases (exists_completed_turn_iff_turn_set before after chosen final).2
        ⟨turn, hafter⟩ with ⟨preparation, trace, hchosen⟩
    exact ⟨final, preparation, trace, hchosen⟩

/-- After a completed turn, the new mover's doubled draw quota is the old waiting player's doubled
draw quota. -/
theorem TurnSet.endpoint_remaining_sum_add_deficit
    {before : GamePosition} {chosen : Finset ℕ} {final : ℕ}
    (turn : TurnSet before chosen final) :
    (completedTurnEndpoint before chosen).remaining.sum (fun x => x) +
        (completedTurnEndpoint before chosen).deficit =
      before.remaining.sum (fun x => x) - before.deficit := by
  have hsum : (before.remaining \ chosen).sum (fun x => x) + chosen.sum (fun x => x) =
      before.remaining.sum (fun x => x) := by
    simpa using Finset.sum_sdiff (f := fun x : ℕ => x) turn.chosen_subset
  have hcatches := turn.catches
  change (before.remaining \ chosen).sum (fun x => x) +
      (chosen.sum (fun x => x) - before.deficit) =
    before.remaining.sum (fun x => x) - before.deficit
  omega

/-- The old mover's doubled residual quota after a completed turn is its old doubled quota minus
twice the turn total. -/
theorem TurnSet.endpoint_remaining_sum_sub_deficit
    {before : GamePosition} {chosen : Finset ℕ} {final : ℕ}
    (turn : TurnSet before chosen final) :
    (completedTurnEndpoint before chosen).remaining.sum (fun x => x) -
        (completedTurnEndpoint before chosen).deficit =
      before.remaining.sum (fun x => x) + before.deficit -
        2 * chosen.sum (fun x => x) := by
  have hsum : (before.remaining \ chosen).sum (fun x => x) + chosen.sum (fun x => x) =
      before.remaining.sum (fun x => x) := by
    simpa using Finset.sum_sdiff (f := fun x : ℕ => x) turn.chosen_subset
  have hcatches := turn.catches
  change (before.remaining \ chosen).sum (fun x => x) -
      (chosen.sum (fun x => x) - before.deficit) =
    before.remaining.sum (fun x => x) + before.deficit -
      2 * chosen.sum (fun x => x)
  omega

/-- A legal pick that leaves the mover behind preserves nonterminality. -/
theorem GamePosition.after_pick_not_terminal_of_lt
    (position : GamePosition) (x : ℕ)
    (hterminal : ¬ position.IsTerminal)
    (hx : position.LegalMove x)
    (hlt : x < position.deficit) :
    ¬ (position.afterPick x).IsTerminal := by
  rw [GamePosition.not_is_terminal_iff] at hterminal ⊢
  rcases hterminal with ⟨hremaining, hcatch⟩
  have hsumErase :
      (position.remaining.erase x).sum (fun y ↦ y) + x =
        position.remaining.sum (fun y ↦ y) := by
    simpa using Finset.sum_erase_add position.remaining (fun y ↦ y) hx
  constructor
  · intro hempty
    change position.remaining.erase x = ∅ at hempty
    rw [hempty] at hsumErase
    simp only [Finset.sum_empty, zero_add] at hsumErase
    omega
  · simp only [GamePosition.afterPick, Position.afterPick, hlt, ite_true]
    omega

/-- Safety for the player taking a completed turn transports backward from its endpoint. -/
theorem CompletedTurn.can_avoid_loss_of_safe_endpoint
    {player : Player} {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after)
    (htoMove : before.toMove = player)
    (hsafe : CanAvoidLoss player after) :
    CanAvoidLoss player before := by
  induction trace with
  | finish position x legal catches =>
      have turn := CompletedTurn.finish position x legal catches
      rw [can_avoid_loss_iff_exists_safe_move player position turn.before_not_terminal htoMove]
      exact ⟨x, legal, hsafe⟩
  | more position x xs after legal behind tail ih =>
      have hchildToMove : (position.afterPick x).toMove = player := by
        rw [GamePosition.to_move_after_pick_of_lt position x behind]
        exact htoMove
      have hchildSafe : CanAvoidLoss player (position.afterPick x) :=
        ih hchildToMove hsafe
      have turn := CompletedTurn.more position x xs after legal behind tail
      rw [can_avoid_loss_iff_exists_safe_move player position turn.before_not_terminal htoMove]
      exact ⟨x, legal, hchildSafe⟩

/-- Safety for the player waiting through a completed turn transports to every endpoint. -/
theorem CompletedTurn.safe_endpoint_of_can_avoid_loss
    {player : Player} {before after : GamePosition} {picks : List ℕ}
    (trace : CompletedTurn before picks after)
    (htoMove : before.toMove ≠ player)
    (hsafe : CanAvoidLoss player before) :
    CanAvoidLoss player after := by
  induction trace with
  | finish position x legal catches =>
      have turn := CompletedTurn.finish position x legal catches
      rw [can_avoid_loss_iff_forall_safe_moves player position turn.before_not_terminal htoMove]
        at hsafe
      exact hsafe x legal
  | more position x xs after legal behind tail ih =>
      have turn := CompletedTurn.more position x xs after legal behind tail
      have hchildSafe : CanAvoidLoss player (position.afterPick x) := by
        rw [can_avoid_loss_iff_forall_safe_moves player position turn.before_not_terminal htoMove]
          at hsafe
        exact hsafe x legal
      have hchildToMove : (position.afterPick x).toMove ≠ player := by
        rw [GamePosition.to_move_after_pick_of_lt position x behind]
        exact htoMove
      exact ih hchildToMove hchildSafe

/-- At a friendly nonterminal node, safety is equivalent to one safe completed-turn trace. -/
theorem can_avoid_loss_iff_exists_safe_completed_turn_trace
    (player : Player) (before : GamePosition)
    (hterminal : ¬ before.IsTerminal)
    (htoMove : before.toMove = player) :
    CanAvoidLoss player before ↔
      ∃ preparation final after,
        CompletedTurn before (preparation ++ [final]) after ∧
          CanAvoidLoss player after := by
  constructor
  · intro hsafe
    rw [can_avoid_loss_iff_exists_safe_move player before hterminal htoMove] at hsafe
    obtain ⟨x, hx, hchildSafe⟩ := hsafe
    by_cases hbehind : x < before.deficit
    · have hchildTerminal : ¬ (before.afterPick x).IsTerminal :=
        before.after_pick_not_terminal_of_lt x hterminal hx hbehind
      have hchildToMove : (before.afterPick x).toMove = player := by
        rw [GamePosition.to_move_after_pick_of_lt before x hbehind]
        exact htoMove
      obtain ⟨preparation, final, after, tail, hsafeAfter⟩ :=
        (can_avoid_loss_iff_exists_safe_completed_turn_trace player (before.afterPick x)
          hchildTerminal hchildToMove).mp hchildSafe
      refine ⟨x :: preparation, final, after, ?_, hsafeAfter⟩
      simpa using CompletedTurn.more before x (preparation ++ [final]) after hx hbehind tail
    · have hcatches : before.deficit ≤ x := by omega
      exact ⟨[], x, before.afterPick x,
        CompletedTurn.finish before x hx hcatches, hchildSafe⟩
  · rintro ⟨preparation, final, after, trace, hsafeAfter⟩
    exact trace.can_avoid_loss_of_safe_endpoint htoMove hsafeAfter
termination_by before.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    assumption

/-- At an adversarial nonterminal node, safety is equivalent to every completed-turn endpoint
being safe. -/
theorem can_avoid_loss_iff_forall_safe_completed_turn_trace
    (player : Player) (before : GamePosition)
    (hterminal : ¬ before.IsTerminal)
    (htoMove : before.toMove ≠ player) :
    CanAvoidLoss player before ↔
      ∀ preparation final after,
        CompletedTurn before (preparation ++ [final]) after →
          CanAvoidLoss player after := by
  constructor
  · intro hsafe preparation final after trace
    exact trace.safe_endpoint_of_can_avoid_loss htoMove hsafe
  · intro hsafe
    rw [can_avoid_loss_iff_forall_safe_moves player before hterminal htoMove]
    intro x hx
    by_cases hbehind : x < before.deficit
    · have hchildTerminal : ¬ (before.afterPick x).IsTerminal :=
        before.after_pick_not_terminal_of_lt x hterminal hx hbehind
      have hchildToMove : (before.afterPick x).toMove ≠ player := by
        rw [GamePosition.to_move_after_pick_of_lt before x hbehind]
        exact htoMove
      apply (can_avoid_loss_iff_forall_safe_completed_turn_trace player (before.afterPick x)
        hchildTerminal hchildToMove).mpr
      intro preparation final after tail
      apply hsafe (x :: preparation) final after
      simpa using CompletedTurn.more before x (preparation ++ [final]) after hx hbehind tail
    · have hcatches : before.deficit ≤ x := by omega
      apply hsafe [] x (before.afterPick x)
      exact CompletedTurn.finish before x hx hcatches
termination_by before.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    assumption

/-- At a friendly node, non-loss is equivalent to the existence of a safe completed-turn
endpoint. -/
theorem can_avoid_loss_iff_exists_safe_turn_set
    (player : Player) (before : GamePosition)
    (hterminal : ¬ before.IsTerminal)
    (htoMove : before.toMove = player) :
    CanAvoidLoss player before ↔
      ∃ chosen final, TurnSet before chosen final ∧
        CanAvoidLoss player (completedTurnEndpoint before chosen) := by
  rw [can_avoid_loss_iff_exists_safe_completed_turn_trace player before hterminal htoMove]
  constructor
  · rintro ⟨preparation, final, after, trace, hsafe⟩
    let chosen := (preparation ++ [final]).toFinset
    have hturnEndpoint :=
      (exists_completed_turn_iff_turn_set before after chosen final).mp
        ⟨preparation, trace, rfl⟩
    refine ⟨chosen, final, hturnEndpoint.1, ?_⟩
    rw [← hturnEndpoint.2]
    exact hsafe
  · rintro ⟨chosen, final, turn, hsafe⟩
    obtain ⟨preparation, trace, _⟩ :=
      (exists_completed_turn_iff_turn_set before
        (completedTurnEndpoint before chosen) chosen final).mpr ⟨turn, rfl⟩
    exact ⟨preparation, final, completedTurnEndpoint before chosen, trace, hsafe⟩

/-- At an adversarial node, non-loss is equivalent to safety at every completed-turn endpoint. -/
theorem can_avoid_loss_iff_forall_safe_turn_sets
    (player : Player) (before : GamePosition)
    (hterminal : ¬ before.IsTerminal)
    (htoMove : before.toMove ≠ player) :
    CanAvoidLoss player before ↔
      ∀ chosen final, TurnSet before chosen final →
        CanAvoidLoss player (completedTurnEndpoint before chosen) := by
  rw [can_avoid_loss_iff_forall_safe_completed_turn_trace player before hterminal htoMove]
  constructor
  · intro hsafe chosen final turn
    obtain ⟨preparation, trace, _⟩ :=
      (exists_completed_turn_iff_turn_set before
        (completedTurnEndpoint before chosen) chosen final).mpr ⟨turn, rfl⟩
    exact hsafe preparation final (completedTurnEndpoint before chosen) trace
  · intro hsafe preparation final after trace
    let chosen := (preparation ++ [final]).toFinset
    have hturnEndpoint :=
      (exists_completed_turn_iff_turn_set before after chosen final).mp
        ⟨preparation, trace, rfl⟩
    rw [hturnEndpoint.2]
    exact hsafe chosen final hturnEndpoint.1

/-- A nonterminal normalized position is non-losing exactly when some completed-turn endpoint is
not winning for the new mover. -/
theorem Position.value_ne_loss_iff_exists_turn_set
    (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit) :
    position.value ≠ .loss ↔
      ∃ chosen final,
        TurnSet ⟨position, .p1⟩ chosen final ∧
          (completedTurnEndpoint ⟨position, .p1⟩ chosen).toPosition.value ≠ .win := by
  let before : GamePosition := ⟨position, .p1⟩
  have hterminal : ¬ before.IsTerminal := by
    rw [GamePosition.not_is_terminal_iff]
    exact ⟨hremaining, hcatch⟩
  have hbridgeBefore :
      CanAvoidLoss .p1 before ↔ position.value ≠ .loss := by
    simpa [before] using can_avoid_loss_iff_value .p1 before
  rw [← hbridgeBefore,
    can_avoid_loss_iff_exists_safe_turn_set .p1 before hterminal rfl]
  constructor
  · rintro ⟨chosen, final, turn, hsafe⟩
    refine ⟨chosen, final, turn, ?_⟩
    rw [can_avoid_loss_iff_value] at hsafe
    simpa [before, completedTurnEndpoint, Player.other] using hsafe
  · rintro ⟨chosen, final, turn, hvalue⟩
    refine ⟨chosen, final, turn, ?_⟩
    rw [can_avoid_loss_iff_value]
    simpa [before, completedTurnEndpoint, Player.other] using hvalue

/-- A nonterminal normalized position is non-winning exactly when every completed-turn endpoint is
non-losing for the new mover. -/
theorem Position.value_ne_win_iff_forall_turn_sets
    (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit) :
    position.value ≠ .win ↔
      ∀ chosen final,
        TurnSet ⟨position, .p1⟩ chosen final →
          (completedTurnEndpoint ⟨position, .p1⟩ chosen).toPosition.value ≠ .loss := by
  let before : GamePosition := ⟨position, .p1⟩
  have hterminal : ¬ before.IsTerminal := by
    rw [GamePosition.not_is_terminal_iff]
    exact ⟨hremaining, hcatch⟩
  have htoMove : before.toMove ≠ .p2 := by simp [before]
  have hbridgeBefore :
      CanAvoidLoss .p2 before ↔ position.value ≠ .win := by
    simpa [before] using can_avoid_loss_iff_value .p2 before
  rw [← hbridgeBefore,
    can_avoid_loss_iff_forall_safe_turn_sets .p2 before hterminal htoMove]
  constructor
  · intro hsafe chosen final turn
    have hsafeEndpoint := hsafe chosen final turn
    rw [can_avoid_loss_iff_value] at hsafeEndpoint
    simpa [before, completedTurnEndpoint, Player.other] using hsafeEndpoint
  · intro hsafe chosen final turn
    rw [can_avoid_loss_iff_value]
    simpa [before, completedTurnEndpoint, Player.other] using hsafe chosen final turn

/-- At positive deficit, non-loss is the existential completed-turn recurrence over legal
subsets. -/
theorem Position.value_ne_loss_iff_exists_completed_turn_subset
    (position : Position)
    (hdeficit : 0 < position.deficit)
    (hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit) :
    position.value ≠ .loss ↔
      ∃ chosen, ∃ hchosen : chosen.Nonempty,
        chosen ⊆ position.remaining ∧
          position.deficit ≤ chosen.sum (fun x ↦ x) ∧
            chosen.sum (fun x ↦ x) < position.deficit + chosen.max' hchosen ∧
              (completedTurnEndpoint ⟨position, .p1⟩ chosen).toPosition.value ≠ .win := by
  have hremaining : position.remaining ≠ ∅ := by
    intro hempty
    apply hcatch
    simpa [hempty] using hdeficit
  rw [position.value_ne_loss_iff_exists_turn_set hremaining hcatch]
  constructor
  · rintro ⟨chosen, final, turn, hvalue⟩
    obtain ⟨hchosen, hsub, hcatches, hbelow⟩ :=
      (exists_turn_set_iff_sum_lt_deficit_add_max ⟨position, .p1⟩ chosen hdeficit).mp
        ⟨final, turn⟩
    exact ⟨chosen, hchosen, hsub, hcatches, hbelow, hvalue⟩
  · rintro ⟨chosen, hchosen, hsub, hcatches, hbelow, hvalue⟩
    obtain ⟨final, turn⟩ :=
      (exists_turn_set_iff_sum_lt_deficit_add_max ⟨position, .p1⟩ chosen hdeficit).mpr
        ⟨hchosen, hsub, hcatches, hbelow⟩
    exact ⟨chosen, final, turn, hvalue⟩

/-- At positive deficit, non-win is the universal completed-turn recurrence over legal subsets. -/
theorem Position.value_ne_win_iff_forall_completed_turn_subsets
    (position : Position)
    (hdeficit : 0 < position.deficit)
    (hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit) :
    position.value ≠ .win ↔
      ∀ chosen, ∀ hchosen : chosen.Nonempty,
        chosen ⊆ position.remaining →
          position.deficit ≤ chosen.sum (fun x ↦ x) →
            chosen.sum (fun x ↦ x) < position.deficit + chosen.max' hchosen →
              (completedTurnEndpoint ⟨position, .p1⟩ chosen).toPosition.value ≠ .loss := by
  have hremaining : position.remaining ≠ ∅ := by
    intro hempty
    apply hcatch
    simpa [hempty] using hdeficit
  rw [position.value_ne_win_iff_forall_turn_sets hremaining hcatch]
  constructor
  · intro hsafe chosen hchosen hsub hcatches hbelow
    obtain ⟨final, turn⟩ :=
      (exists_turn_set_iff_sum_lt_deficit_add_max ⟨position, .p1⟩ chosen hdeficit).mpr
        ⟨hchosen, hsub, hcatches, hbelow⟩
    exact hsafe chosen final turn
  · intro hsafe chosen final turn
    obtain ⟨hchosen, hsub, hcatches, hbelow⟩ :=
      (exists_turn_set_iff_sum_lt_deficit_add_max ⟨position, .p1⟩ chosen hdeficit).mp
        ⟨final, turn⟩
    exact hsafe chosen hchosen hsub hcatches hbelow

/-- A nonterminal normalized position draws exactly when all completed-turn endpoints are
non-losing for the new mover and at least one such endpoint draws. -/
theorem Position.value_eq_draw_iff_turn_sets
    (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcatch : ¬ position.remaining.sum (fun x ↦ x) < position.deficit) :
    position.value = .draw ↔
      (∀ chosen final,
        TurnSet ⟨position, .p1⟩ chosen final →
          (completedTurnEndpoint ⟨position, .p1⟩ chosen).toPosition.value ≠ .loss) ∧
      ∃ chosen final,
        TurnSet ⟨position, .p1⟩ chosen final ∧
          (completedTurnEndpoint ⟨position, .p1⟩ chosen).toPosition.value = .draw := by
  constructor
  · intro hdraw
    have hparts := (Outcome.eq_draw_iff position.value).mp hdraw
    have hall :=
      (position.value_ne_win_iff_forall_turn_sets hremaining hcatch).mp hparts.2
    obtain ⟨chosen, final, turn, hneWin⟩ :=
      (position.value_ne_loss_iff_exists_turn_set hremaining hcatch).mp hparts.1
    refine ⟨hall, chosen, final, turn, ?_⟩
    exact (Outcome.eq_draw_iff _).mpr ⟨hall chosen final turn, hneWin⟩
  · rintro ⟨hall, chosen, final, turn, hdraw⟩
    apply (Outcome.eq_draw_iff position.value).mpr
    constructor
    · apply (position.value_ne_loss_iff_exists_turn_set hremaining hcatch).mpr
      refine ⟨chosen, final, turn, ?_⟩
      exact ((Outcome.eq_draw_iff _).mp hdraw).2
    · exact (position.value_ne_win_iff_forall_turn_sets hremaining hcatch).mpr hall

end CatchUp
