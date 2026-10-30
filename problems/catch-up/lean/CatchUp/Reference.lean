/-
Copyright 2025 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Reference.lean, vendored there from formal-conjectures.
Modified for solverz: ported to Lean/Mathlib v4.35.0; `Outcome`, `Outcome.neg`, `Outcome.best`,
`valueAux` and `value` come from `CatchUp.Statement` instead of being redefined; module system.
-/
module

public import CatchUp.Statement
public import Mathlib.Logic.Relation

/-!
# The normalized game

Infrastructure for the verified evaluator. `Position ⟨R, d⟩` is a position after the opening seen
from the mover, who is `d` behind; `Position.value` is its value, and
`Position.value_eq_value_aux` shows it equals `valueAux R s (s + d) false`, our `V(R, d)`.
`CanAvoidLoss` is one-sided safety for a fixed player; `can_avoid_loss_iff_value` ties it to
`Position.value`.
-/

@[expose] public section

namespace CatchUp

/--
An arbitrary two elements type indexing the players in the Catch-Up game.
-/
inductive Player
  | p1
  | p2
deriving DecidableEq, Repr

/-- Returns the other player. -/
def Player.other : Player → Player
  | p1 => p2
  | p2 => p1

/-- Switching players gives `other` exactly when the two original players differ. -/
@[simp]
theorem Player.other_eq_iff_ne (p q : Player) :
    p.other = q ↔ p ≠ q := by
  cases p <;> cases q <;> simp [Player.other]


/-- Negating an outcome avoids a loss exactly when the original outcome is not a win. -/
@[simp]
theorem Outcome.neg_ne_loss_iff (outcome : Outcome) :
    outcome.neg ≠ .loss ↔ outcome ≠ .win := by
  cases outcome <;> simp [Outcome.neg]

/-- Negating an outcome avoids a win exactly when the original outcome is not a loss. -/
@[simp]
theorem Outcome.neg_ne_win_iff (outcome : Outcome) :
    outcome.neg ≠ .win ↔ outcome ≠ .loss := by
  cases outcome <;> simp [Outcome.neg]

/-- The best listed outcome avoids a loss exactly when some listed outcome does. -/
@[simp]
theorem Outcome.best_ne_loss_iff (outcomes : List Outcome) :
    Outcome.best outcomes ≠ .loss ↔ ∃ outcome ∈ outcomes, outcome ≠ .loss := by
  let combine : Outcome → Outcome → Outcome := fun
    | .win, _ => .win
    | _, .win => .win
    | .draw, _ => .draw
    | _, .draw => .draw
    | _, _ => .loss
  have foldl_ne_loss_iff (accumulator : Outcome) :
      outcomes.foldl combine accumulator ≠ .loss ↔
        accumulator ≠ .loss ∨ ∃ outcome ∈ outcomes, outcome ≠ .loss := by
    induction outcomes generalizing accumulator with
    | nil => simp
    | cons head tail ih =>
        rw [List.foldl_cons, ih]
        cases accumulator <;> cases head <;> simp [combine]
  change outcomes.foldl combine .loss ≠ .loss ↔ _
  simpa using foldl_ne_loss_iff .loss

/-- The best listed outcome avoids a win exactly when every listed outcome does. -/
@[simp]
theorem Outcome.best_ne_win_iff (outcomes : List Outcome) :
    Outcome.best outcomes ≠ .win ↔ ∀ outcome ∈ outcomes, outcome ≠ .win := by
  let combine : Outcome → Outcome → Outcome := fun
    | .win, _ => .win
    | _, .win => .win
    | .draw, _ => .draw
    | _, .draw => .draw
    | _, _ => .loss
  have foldl_ne_win_iff (accumulator : Outcome) :
      outcomes.foldl combine accumulator ≠ .win ↔
        accumulator ≠ .win ∧ ∀ outcome ∈ outcomes, outcome ≠ .win := by
    induction outcomes generalizing accumulator with
    | nil => simp
    | cons head tail ih =>
        rw [List.foldl_cons, ih]
        cases accumulator <;> cases head <;> simp [combine]
  change outcomes.foldl combine .loss ≠ .win ↔ _
  simpa using foldl_ne_win_iff .loss

/-- An outcome is a draw exactly when it is neither a loss nor a win. -/
@[simp]
theorem Outcome.eq_draw_iff (outcome : Outcome) :
    outcome = .draw ↔ outcome ≠ .loss ∧ outcome ≠ .win := by
  cases outcome <;> simp

/--
A Catch-Up position after the first move, viewed from the player who is currently picking.

The current player is tied or behind, and `deficit` is the opponent's score minus the current
player's score. Thus the absolute scores are not recorded.
-/
structure Position where
  remaining : Finset ℕ
  deficit : ℕ
deriving DecidableEq

/--
A post-opening Catch-Up position together with the identity of the player currently picking.

The inherited `Position` is viewed from `toMove`'s perspective: its `deficit` is the other player's
score minus `toMove`'s score.
-/
structure GamePosition extends Position where
  toMove : Player
deriving DecidableEq

/-- A counter is a legal move exactly when it remains available. -/
def GamePosition.LegalMove (position : GamePosition) (x : ℕ) : Prop :=
  x ∈ position.remaining

/-- The normalized position after the current player picks `x`. -/
def Position.afterPick (position : Position) (x : ℕ) : Position :=
  ⟨position.remaining.erase x,
    if x < position.deficit then position.deficit - x else x - position.deficit⟩

/--
The absolute post-opening position after the current player picks `x`.

As with `Position.afterPick`, this function is total; `GamePosition.LegalMove` records legality.
-/
def GamePosition.afterPick (position : GamePosition) (x : ℕ) : GamePosition :=
  ⟨position.toPosition.afterPick x,
    if x < position.deficit then position.toMove else position.toMove.other⟩

/-- Forgetting the player after a pick gives the corresponding normalized transition. -/
@[simp]
theorem GamePosition.to_position_after_pick (position : GamePosition) (x : ℕ) :
    (position.afterPick x).toPosition = position.toPosition.afterPick x := by
  rfl

/-- An absolute transition removes the chosen counter. -/
@[simp]
theorem GamePosition.remaining_after_pick (position : GamePosition) (x : ℕ) :
    (position.afterPick x).remaining = position.remaining.erase x := by
  rfl

/-- A player who remains behind after picking continues the same turn. -/
@[simp]
theorem GamePosition.to_move_after_pick_of_lt (position : GamePosition) (x : ℕ)
    (hx : x < position.deficit) :
    (position.afterPick x).toMove = position.toMove := by
  simp [GamePosition.afterPick, hx]

/-- A player who catches up after picking ends the turn. -/
@[simp]
theorem GamePosition.to_move_after_pick_of_le (position : GamePosition) (x : ℕ)
    (hx : position.deficit ≤ x) :
    (position.afterPick x).toMove = position.toMove.other := by
  simp [GamePosition.afterPick, not_lt_of_ge hx]

/-- A legal absolute transition strictly decreases the number of remaining counters. -/
theorem GamePosition.remaining_card_after_pick_lt (position : GamePosition) (x : ℕ)
    (hx : position.LegalMove x) :
    (position.afterPick x).remaining.card < position.remaining.card := by
  change (position.remaining.erase x).card < position.remaining.card
  exact Finset.card_erase_lt_of_mem hx

/-- A position is terminal when no counters remain or the current player cannot catch up. -/
def GamePosition.IsTerminal (position : GamePosition) : Prop :=
  position.remaining = ∅ ∨
    position.remaining.sum (fun x => x) < position.deficit

instance (position : GamePosition) : Decidable position.IsTerminal := by
  unfold GamePosition.IsTerminal
  infer_instance

/-- A legal post-opening step chooses an available counter from a nonterminal position. -/
def GamePosition.Step (before after : GamePosition) : Prop :=
  ¬ before.IsTerminal ∧
    ∃ x, before.LegalMove x ∧ after = before.afterPick x

/-- Picking a legal counter from a nonterminal position gives a game step. -/
theorem GamePosition.step_after_pick (position : GamePosition) (x : ℕ)
    (hterminal : ¬ position.IsTerminal) (hx : position.LegalMove x) :
    position.Step (position.afterPick x) := by
  exact ⟨hterminal, x, hx, rfl⟩

/--
The outcome of a terminal position from a fixed player's perspective.

This total function is intended to be used when `position.IsTerminal` holds.
-/
def GamePosition.terminalOutcomeFor (position : GamePosition) (player : Player) : Outcome :=
  if position.deficit = 0 then .draw
  else if position.toMove = player then .loss
  else .win

/-- A position with no remaining counters is terminal. -/
theorem GamePosition.is_terminal_of_remaining_eq_empty (position : GamePosition)
    (hremaining : position.remaining = ∅) :
    position.IsTerminal := by
  exact Or.inl hremaining

/-- A position where the current player cannot catch up is terminal. -/
theorem GamePosition.is_terminal_of_sum_lt_deficit (position : GamePosition)
    (hsum : position.remaining.sum (fun x => x) < position.deficit) :
    position.IsTerminal := by
  exact Or.inr hsum

/-- A position is nonterminal exactly when it is nonempty and catching up remains possible. -/
@[simp]
theorem GamePosition.not_is_terminal_iff (position : GamePosition) :
    ¬ position.IsTerminal ↔
      position.remaining ≠ ∅ ∧
        ¬ position.remaining.sum (fun x => x) < position.deficit := by
  simp [GamePosition.IsTerminal]

/-- A zero-deficit terminal position is a draw for either player. -/
@[simp]
theorem GamePosition.terminal_outcome_for_eq_draw (position : GamePosition) (player : Player)
    (hdeficit : position.deficit = 0) :
    position.terminalOutcomeFor player = .draw := by
  simp [GamePosition.terminalOutcomeFor, hdeficit]

/-- At a positive-deficit terminal position, the player who is currently moving loses. -/
@[simp]
theorem GamePosition.terminal_outcome_for_to_move_eq_loss (position : GamePosition)
    (hdeficit : position.deficit ≠ 0) :
    position.terminalOutcomeFor position.toMove = .loss := by
  simp [GamePosition.terminalOutcomeFor, hdeficit]

/-- At a positive-deficit terminal position, the other player wins. -/
@[simp]
theorem GamePosition.terminal_outcome_for_eq_win (position : GamePosition) (player : Player)
    (hdeficit : position.deficit ≠ 0) (hplayer : position.toMove ≠ player) :
    position.terminalOutcomeFor player = .win := by
  simp [GamePosition.terminalOutcomeFor, hdeficit, hplayer]

/--
A fixed player can avoid losing from an absolute post-opening position.

At the fixed player's nodes, some legal move must remain safe. At the opponent's nodes, every legal
move must remain safe.
-/
def CanAvoidLoss (player : Player) (position : GamePosition) : Prop :=
  if position.IsTerminal then
    position.terminalOutcomeFor player ≠ .loss
  else if position.toMove = player then
    ∃ x, ∃ _ : position.LegalMove x, CanAvoidLoss player (position.afterPick x)
  else
    ∀ x, position.LegalMove x → CanAvoidLoss player (position.afterPick x)
termination_by position.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    assumption

/-- At a terminal node, non-loss means that the fixed player's terminal outcome is not a loss. -/
theorem can_avoid_loss_iff_terminal_outcome_ne_loss (player : Player) (position : GamePosition)
    (hterminal : position.IsTerminal) :
    CanAvoidLoss player position ↔ position.terminalOutcomeFor player ≠ .loss := by
  rw [CanAvoidLoss.eq_def]
  simp [hterminal]

/-- At a friendly nonterminal node, non-loss means that some legal move remains safe. -/
theorem can_avoid_loss_iff_exists_safe_move (player : Player) (position : GamePosition)
    (hterminal : ¬ position.IsTerminal) (htoMove : position.toMove = player) :
    CanAvoidLoss player position ↔
      ∃ x, position.LegalMove x ∧ CanAvoidLoss player (position.afterPick x) := by
  rw [CanAvoidLoss.eq_def]
  simp [hterminal, htoMove]

/-- At an adversarial nonterminal node, non-loss must survive every legal move. -/
theorem can_avoid_loss_iff_forall_safe_moves (player : Player) (position : GamePosition)
    (hterminal : ¬ position.IsTerminal) (htoMove : position.toMove ≠ player) :
    CanAvoidLoss player position ↔
      ∀ x, position.LegalMove x → CanAvoidLoss player (position.afterPick x) := by
  rw [CanAvoidLoss.eq_def]
  simp [hterminal, htoMove]

/--
The game-theoretic value of a post-opening Catch-Up position, from the current player's perspective.

If the current deficit is $d$ and the player takes $x$, then:
* if $x < d$, the player remains behind by $d-x$ and continues picking;
* if $d \leq x$, the turn passes and the other player is behind by $x-d$.
-/
noncomputable def Position.value (position : Position) : Outcome :=
  if position.remaining = ∅ then
    if position.deficit = 0 then .draw else .loss
  else if position.remaining.sum (fun x => x) < position.deficit then
    .loss
  else
    let moves := position.remaining.attach.toList
    let outcomes := moves.map fun ⟨x, _⟩ =>
      let next := position.afterPick x
      if x < position.deficit then
        Position.value next
      else
        (Position.value next).neg
    .best outcomes
termination_by position.remaining.card
decreasing_by
  all_goals
    simpa [Position.afterPick] using Finset.card_erase_lt_of_mem ‹_›

/-- The normalized and score-based evaluators agree when the current player is not ahead. -/
theorem Position.value_eq_value_aux (remaining : Finset ℕ) (s_me s_opp : ℕ)
    (hle : s_me ≤ s_opp) :
    Position.value ⟨remaining, s_opp - s_me⟩ = valueAux remaining s_me s_opp false := by
  induction remaining using Finset.strongInduction generalizing s_me s_opp with
  | H remaining ih =>
      rw [Position.value.eq_def, valueAux.eq_def]
      by_cases hempty : remaining = ∅
      · subst remaining
        simp only [ite_true]
        rcases hle.eq_or_lt with rfl | hlt
        · simp
        · have hdeficit_ne : s_opp - s_me ≠ 0 := by omega
          have hnot_ahead : ¬ s_opp < s_me := by omega
          simp only [hdeficit_ne, hnot_ahead, hlt, ite_false, ite_true]
      · have hprune :
            (remaining.sum (fun x => x) < s_opp - s_me) ↔
              (s_me + remaining.sum (fun x => x) < s_opp) := by
          omega
        simp only [hempty, ite_false]
        simp only [hprune]
        by_cases hlose : s_me + remaining.sum (fun x => x) < s_opp
        · simp only [hlose, ite_true]
        · simp only [hlose, ite_false]
          simp only [Bool.false_eq_true]
          simp only [ite_false]
          congr 1
          apply List.map_congr_left
          rintro ⟨x, hx⟩ _
          change (if x < s_opp - s_me then
              (Position.afterPick ⟨remaining, s_opp - s_me⟩ x).value
            else (Position.afterPick ⟨remaining, s_opp - s_me⟩ x).value.neg) =
            if s_me + x ≥ s_opp then (valueAux (remaining.erase x) s_opp (s_me + x) false).neg
            else valueAux (remaining.erase x) (s_me + x) s_opp false
          by_cases hcontinue : x < s_opp - s_me
          · have hstill : s_me + x < s_opp := by omega
            simp only [hcontinue, ite_true, not_le_of_gt hstill, ite_false]
            have hih := ih (remaining.erase x) (Finset.erase_ssubset hx)
              (s_me + x) s_opp hstill.le
            have hdeficit : (s_opp - s_me) - x = s_opp - (s_me + x) := by omega
            simpa [Position.afterPick, hcontinue, hdeficit] using hih
          · have hswitch : s_opp ≤ s_me + x := by omega
            simp only [hcontinue, ite_false, hswitch, ite_true]
            congr 1
            have hih := ih (remaining.erase x) (Finset.erase_ssubset hx)
              s_opp (s_me + x) hswitch
            have hdeficit : x - (s_opp - s_me) = s_me + x - s_opp := by omega
            simpa [Position.afterPick, hcontinue, hdeficit] using hih

/-- The outcome obtained by choosing `x`, from the current player's perspective. -/
noncomputable def Position.moveOutcome (position : Position) (x : ℕ) : Outcome :=
  let next := position.afterPick x
  if x < position.deficit then next.value else next.value.neg

/-- A nonterminal position is valued by taking the best outcome among its available moves. -/
theorem Position.value_eq_best_move_outcome (position : Position)
    (hremaining : position.remaining ≠ ∅)
    (hcanCatch : ¬position.remaining.sum (fun x => x) < position.deficit) :
    position.value =
      .best (position.remaining.attach.toList.map fun ⟨x, _⟩ => position.moveOutcome x) := by
  rw [Position.value.eq_def]
  simp only [hremaining, hcanCatch, ite_false]
  simp only [Position.moveOutcome]

/-- One-sided safety agrees with the minimax value from the player-to-move perspective. -/
theorem can_avoid_loss_iff_value (player : Player) (position : GamePosition) :
    CanAvoidLoss player position ↔
      if position.toMove = player then
        position.toPosition.value ≠ .loss
      else
        position.toPosition.value ≠ .win := by
  by_cases hterminal : position.IsTerminal
  · rw [can_avoid_loss_iff_terminal_outcome_ne_loss player position hterminal]
    rw [Position.value.eq_def]
    rcases hterminal with hremaining | hsum
    · by_cases hdeficit : position.deficit = 0 <;>
        by_cases htoMove : position.toMove = player <;>
        simp [hremaining, GamePosition.terminalOutcomeFor, hdeficit, htoMove]
    · by_cases hremaining : position.remaining = ∅
      · by_cases hdeficit : position.deficit = 0 <;>
          by_cases htoMove : position.toMove = player <;>
          simp [hremaining, GamePosition.terminalOutcomeFor, hdeficit, htoMove]
      · have hdeficit : position.deficit ≠ 0 := by omega
        simp [hremaining, hsum, GamePosition.terminalOutcomeFor, hdeficit]
  · obtain ⟨hremaining, hcanCatch⟩ := position.not_is_terminal_iff.mp hterminal
    rw [Position.value_eq_best_move_outcome position.toPosition hremaining hcanCatch]
    by_cases htoMove : position.toMove = player
    · simp only [htoMove, ite_true]
      rw [can_avoid_loss_iff_exists_safe_move player position hterminal htoMove]
      rw [Outcome.best_ne_loss_iff]
      have move_ne_loss_iff (x : ℕ) (hx : position.LegalMove x) :
          CanAvoidLoss player (position.afterPick x) ↔
            position.toPosition.moveOutcome x ≠ .loss := by
        rw [can_avoid_loss_iff_value player (position.afterPick x)]
        by_cases hcontinue : x < position.deficit
        · simp [Position.moveOutcome, hcontinue, htoMove]
        · have hcatch : position.deficit ≤ x := by omega
          simp [Position.moveOutcome, hcontinue, hcatch, htoMove]
      constructor
      · rintro ⟨x, hx, hsafe⟩
        refine ⟨position.toPosition.moveOutcome x, ?_, (move_ne_loss_iff x hx).mp hsafe⟩
        apply List.mem_map.mpr
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
      · rintro ⟨outcome, houtcome, hsafe⟩
        rcases List.mem_map.mp houtcome with ⟨⟨x, hx⟩, _, rfl⟩
        exact ⟨x, hx, (move_ne_loss_iff x hx).mpr hsafe⟩
    · simp only [htoMove, ite_false]
      rw [can_avoid_loss_iff_forall_safe_moves player position hterminal htoMove]
      rw [Outcome.best_ne_win_iff]
      have move_ne_win_iff (x : ℕ) (hx : position.LegalMove x) :
          CanAvoidLoss player (position.afterPick x) ↔
            position.toPosition.moveOutcome x ≠ .win := by
        rw [can_avoid_loss_iff_value player (position.afterPick x)]
        by_cases hcontinue : x < position.deficit
        · simp [Position.moveOutcome, hcontinue, htoMove]
        · have hcatch : position.deficit ≤ x := by omega
          simp [Position.moveOutcome, hcontinue, hcatch, htoMove]
      constructor
      · intro hsafe outcome houtcome
        rcases List.mem_map.mp houtcome with ⟨⟨x, hx⟩, _, rfl⟩
        exact (move_ne_win_iff x hx).mp (hsafe x hx)
      · intro houtcomes x hx
        apply (move_ne_win_iff x hx).mpr
        apply houtcomes (position.toPosition.moveOutcome x)
        apply List.mem_map.mpr
        exact ⟨⟨x, hx⟩, by simp, rfl⟩
termination_by position.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    assumption

/-- The normalized position after player 1 takes `x` as the opening move from `S`. -/
def afterOpening (S : Finset ℕ) (x : ℕ) : Position :=
  ⟨S.erase x, x⟩

/-- The absolute position after player 1 makes the forced opening pick. -/
def GamePosition.afterOpening (S : Finset ℕ) (x : ℕ) : GamePosition :=
  ⟨CatchUp.afterOpening S x, .p2⟩

/-- Forgetting the next player recovers the normalized post-opening position. -/
@[simp]
theorem GamePosition.to_position_after_opening (S : Finset ℕ) (x : ℕ) :
    (GamePosition.afterOpening S x).toPosition = CatchUp.afterOpening S x := by
  rfl

/-- Player 2 is the next player after player 1's forced opening pick. -/
@[simp]
theorem GamePosition.to_move_after_opening (S : Finset ℕ) (x : ℕ) :
    (GamePosition.afterOpening S x).toMove = .p2 := by
  rfl

/-- The opening counter is removed from the remaining set. -/
@[simp]
theorem GamePosition.remaining_after_opening (S : Finset ℕ) (x : ℕ) :
    (GamePosition.afterOpening S x).remaining = S.erase x := by
  rfl

/-- Player 2's deficit after the opening pick is the value of that counter. -/
@[simp]
theorem GamePosition.deficit_after_opening (S : Finset ℕ) (x : ℕ) :
    (GamePosition.afterOpening S x).deficit = x := by
  rfl

/--
An absolute position reachable after player 1 legally opens the interval game with `x`.
-/
def ReachableFromOpening (N x : ℕ) (position : GamePosition) : Prop :=
  x ∈ Finset.Icc 1 N ∧
    Relation.ReflTransGen GamePosition.Step
      (GamePosition.afterOpening (Finset.Icc 1 N) x) position

/-- Every legal opening produces a reachable post-opening root. -/
theorem reachable_from_opening_root (N x : ℕ) (hx : x ∈ Finset.Icc 1 N) :
    ReachableFromOpening N x (GamePosition.afterOpening (Finset.Icc 1 N) x) := by
  exact ⟨hx, Relation.ReflTransGen.refl⟩

/-- Reachability from a legal opening is preserved by one legal game step. -/
theorem ReachableFromOpening.step {N x : ℕ} {before after : GamePosition}
    (hreachable : ReachableFromOpening N x before) (hstep : before.Step after) :
    ReachableFromOpening N x after := by
  exact ⟨hreachable.1, hreachable.2.tail hstep⟩

/-- Every available pick from a reachable nonterminal position remains reachable. -/
theorem ReachableFromOpening.after_pick {N opening : ℕ} {position : GamePosition}
    (hreachable : ReachableFromOpening N opening position) (x : ℕ)
    (hterminal : ¬ position.IsTerminal) (hx : position.LegalMove x) :
    ReachableFromOpening N opening (position.afterPick x) := by
  exact hreachable.step (position.step_after_pick x hterminal hx)

/-- Add the four counters immediately above `N` to a normalized Catch-Up position. -/
def Position.addFourCounters (position : Position) (N : ℕ) : Position :=
  ⟨position.remaining ∪ Finset.Icc (N + 1) (N + 4), position.deficit⟩

/-- Adding four counters to a post-opening position gives the corresponding larger position. -/
theorem Position.add_four_counters_after_opening (N x : ℕ) (hx : x ∈ Finset.Icc 1 N) :
    (afterOpening (Finset.Icc 1 N) x).addFourCounters N =
      afterOpening (Finset.Icc 1 (N + 4)) x := by
  simp only [Position.addFourCounters, afterOpening]
  congr 1
  ext y
  simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_Icc]
  simp only [Finset.mem_Icc] at hx
  omega

/-- Adding four new counters does not change the availability of an old counter. -/
theorem Position.mem_add_four_counters_iff_of_le (position : Position) (N x : ℕ) (hx : x ≤ N) :
    x ∈ (position.addFourCounters N).remaining ↔ x ∈ position.remaining := by
  simp only [Position.addFourCounters, Finset.mem_union, Finset.mem_Icc]
  have hx_top : ¬(N + 1 ≤ x ∧ x ≤ N + 4) := by omega
  simp only [hx_top, or_false]

/-- Taking an old counter commutes with adding the four new counters. -/
theorem Position.after_pick_add_four_counters (position : Position) (N x : ℕ) (hx : x ≤ N) :
    (position.addFourCounters N).afterPick x = (position.afterPick x).addFourCounters N := by
  simp only [Position.afterPick, Position.addFourCounters]
  congr 1
  have hx_top : x ∉ Finset.Icc (N + 1) (N + 4) := by
    simp only [Finset.mem_Icc]
    omega
  rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem hx_top]

/-- An old move's outcome is preserved when the corresponding child value is preserved. -/
theorem Position.move_outcome_add_four_counters_of_value_eq (position : Position) (N x : ℕ)
    (hx : x ≤ N)
    (hvalue : ((position.afterPick x).addFourCounters N).value = (position.afterPick x).value) :
    (position.addFourCounters N).moveOutcome x = position.moveOutcome x := by
  simp only [Position.moveOutcome]
  rw [Position.after_pick_add_four_counters position N x hx]
  change (if x < position.deficit then ((position.afterPick x).addFourCounters N).value
    else ((position.afterPick x).addFourCounters N).value.neg) = _
  rw [hvalue]

/-- The normalized and score-based evaluators agree on a tied terminal position. -/
theorem position_value_empty_test :
    (Position.value ⟨∅, 0⟩) = valueAux ∅ 4 4 false := by
  rw [Position.value.eq_def, valueAux.eq_def]
  simp

/-- The normalized and score-based evaluators agree when catching up is impossible. -/
theorem position_value_cannot_catch_up_test :
    (Position.value ⟨{1}, 2⟩) = valueAux {1} 4 6 false := by
  rw [Position.value.eq_def, valueAux.eq_def]
  simp

/-- The normalized and score-based evaluators agree when a pick ends the turn. -/
theorem position_value_singleton_test :
    (Position.value ⟨{3}, 2⟩) = valueAux {3} 0 2 false := by
  rw [Position.value.eq_def, valueAux.eq_def]
  simp only [Finset.singleton_ne_empty, ↓reduceIte, Finset.sum_singleton, Nat.reduceLT, zero_add,
    Bool.false_eq_true, ge_iff_le]
  congr 1
  congr 1
  funext x
  have hx : (x : ℕ) = 3 := Finset.mem_singleton.mp x.property
  rw [hx]
  simp only [Nat.reduceLT, ↓reduceIte, Nat.reduceLeDiff, Finset.erase_singleton]
  rw [Position.value.eq_def, valueAux.eq_def]
  simp [Position.afterPick]

/-- A nonempty Catch-Up game is valued by the best negated post-opening outcome. -/
theorem value_eq_best_after_opening (S : Finset ℕ) (hS : S.Nonempty) :
    value S =
      .best (S.attach.toList.map fun ⟨x, _⟩ => (afterOpening S x).value.neg) := by
  rw [value, valueAux.eq_def]
  have hne : S ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hS
  simp only [hne, Nat.zero_add, Nat.not_lt_zero, ite_false, ite_true]
  congr 1
  apply List.map_congr_left
  rintro ⟨x, _⟩ _
  change (valueAux (S.erase x) 0 x false).neg = (afterOpening S x).value.neg
  congr 1
  have hbridge := Position.value_eq_value_aux (S.erase x) 0 x (Nat.zero_le x)
  simpa [afterOpening] using hbridge.symm

/--
A nonempty Catch-Up game is a draw exactly when player 1 can avoid losing after some opening and
player 2 can avoid losing after every opening.
-/
theorem value_eq_draw_iff_can_avoid_loss_after_opening (S : Finset ℕ) (hS : S.Nonempty) :
    value S = .draw ↔
      (∃ x ∈ S, CanAvoidLoss .p1 (GamePosition.afterOpening S x)) ∧
      (∀ x ∈ S, CanAvoidLoss .p2 (GamePosition.afterOpening S x)) := by
  rw [value_eq_best_after_opening S hS, Outcome.eq_draw_iff,
    Outcome.best_ne_loss_iff, Outcome.best_ne_win_iff]
  simp [can_avoid_loss_iff_value]

/-- Catch-Up on `{1, ..., N}` is valued by its post-opening positions when `1 ≤ N`. -/
theorem value_Icc_eq_best_after_opening (N : ℕ) (hN : 1 ≤ N) :
    value (Finset.Icc 1 N) =
      .best ((Finset.Icc 1 N).attach.toList.map fun ⟨x, _⟩ =>
        (afterOpening (Finset.Icc 1 N) x).value.neg) := by
  exact value_eq_best_after_opening (Finset.Icc 1 N) (Finset.nonempty_Icc.mpr hN)

/-- The interval post-opening decomposition applies at the smallest nonempty game. -/
theorem value_Icc_one_post_opening_test :
    value (Finset.Icc 1 1) =
      .best ((Finset.Icc 1 1).attach.toList.map fun ⟨x, _⟩ =>
        (afterOpening (Finset.Icc 1 1) x).value.neg) := by
  exact value_Icc_eq_best_after_opening 1 le_rfl

/-- The interval post-opening decomposition specializes to the paper's four-counter example. -/
theorem value_Icc_four_post_opening_test :
    value (Finset.Icc 1 4) =
      .best ((Finset.Icc 1 4).attach.toList.map fun ⟨x, _⟩ =>
        (afterOpening (Finset.Icc 1 4) x).value.neg) := by
  exact value_Icc_eq_best_after_opening 4 (by omega)

end CatchUp
