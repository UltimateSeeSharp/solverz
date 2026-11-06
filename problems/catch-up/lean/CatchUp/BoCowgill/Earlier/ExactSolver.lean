/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/ExactSolver.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.StrategyContract

/-!
# Catch-Up normalized exact solver

This research solver evaluates every legal move of every visited normalized Catch-Up state. Its
transposition table is keyed by `(remainingMask, deficit, toMove)`, and its exported nodes implement
the complete solved-graph contract from `CatchUp.Earlier.StrategyContract`.

The solver is executable evidence, not a proof of its own correctness. This file therefore also
contains an independent list-based reference recurrence used for small deterministic regression
tests. A later certificate checker will recompute transitions independently of both solvers.

Run with:

```bash
lake env lean --run scripts/catch_up/ExactSolverMain.lean
```
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.ExactSolver

open CatchUp

/-- The memoized solved graph under construction. -/
abbrev Cache := Std.HashMap CacheKey SolvedNode

/-- Solver computations combine a mutable transposition table with explicit failure. -/
abbrev SolverM := StateT Cache (Except String)

/-- A bitmask whose lowest `gameSize` bits are set. -/
def fullMask (gameSize : ℕ) : ℕ :=
  (Nat.shiftLeft 1 gameSize) - 1

/-- The set bits of `remainingMask`, paired with their represented counters. -/
def availableMoves (gameSize remainingMask : ℕ) : List (ℕ × ℕ) :=
  (List.range gameSize).filterMap fun index =>
    if remainingMask.testBit index then some (index, index + 1) else none

/-- Sum the counters represented by a mask. -/
def remainingSum (gameSize remainingMask : ℕ) : ℕ :=
  ((availableMoves gameSize remainingMask).map fun move => move.2).sum

/-- Remove a counter whose bit index is known to be set. -/
def eraseMove (remainingMask index : ℕ) : ℕ :=
  remainingMask - Nat.shiftLeft 1 index

/-- Compute the absolute normalized child of one available move. -/
def nextState (state : State) (index counter : ℕ) : State :=
  let continues := counter < state.deficit
  { remainingMask := eraseMove state.remainingMask index
    deficit := if continues then state.deficit - counter else counter - state.deficit
    toMove := if continues then state.toMove else state.toMove.other }

/-- Return the current mover's outcome exactly when the state is terminal. -/
def terminalOutcome? (gameSize : ℕ) (state : State) : Option Outcome :=
  if state.remainingMask = 0 then
    some <| if state.deficit = 0 then .draw else .loss
  else if remainingSum gameSize state.remainingMask < state.deficit then
    some .loss
  else
    none

/-- Take the best parent-perspective outcome from a complete move list. -/
def bestOutcome (moves : List MoveEvaluation) : Outcome :=
  Outcome.best <| moves.map fun move => move.outcome

/--
Memoized exact evaluation retaining every legal edge.

`fuel` bounds the number of counters that may still be removed. Reaching zero at a nonterminal
state is reported as an error rather than converted into an outcome.
-/
def solveAux (gameSize : ℕ) : ℕ → State → SolverM SolvedNode
  | 0, state =>
      match terminalOutcome? gameSize state with
      | some outcome => pure ⟨state, outcome, []⟩
      | none => throw s!"solver fuel exhausted at {repr state}"
  | fuel + 1, state => do
      if let some cached := (← get)[state.cacheKey]? then
        return cached
      let node ←
        match terminalOutcome? gameSize state with
        | some outcome => pure ⟨state, outcome, []⟩
        | none => do
            let mut moves := []
            for (index, counter) in availableMoves gameSize state.remainingMask do
              let childState := nextState state index counter
              let child ← solveAux gameSize fuel childState
              let outcome :=
                if counter < state.deficit then child.outcome else child.outcome.neg
              moves := ⟨counter, childState, outcome⟩ :: moves
            let orderedMoves := moves.reverse
            pure ⟨state, bestOutcome orderedMoves, orderedMoves⟩
      modify fun cache => cache.insert state.cacheKey node
      return node

/-- Solve one normalized state with enough fuel for every interval-game mask of this size. -/
def solveState (gameSize : ℕ) (state : State) : Except String (SolvedNode × Cache) :=
  (solveAux gameSize (gameSize + 1) state).run {}

/-- A stable numeric order on players used only for deterministic serialization. -/
def playerRank : Player → ℕ
  | .p1 => 0
  | .p2 => 1

/-- Lexicographic comparison of exported states. -/
def stateLE (left right : State) : Bool :=
  if left.remainingMask < right.remainingMask then true
  else if right.remainingMask < left.remainingMask then false
  else if left.deficit < right.deficit then true
  else if right.deficit < left.deficit then false
  else decide (playerRank left.toMove ≤ playerRank right.toMove)

/-- Convert the internal transposition table to a deterministic node list. -/
def sortedNodes (cache : Cache) : List SolvedNode :=
  (cache.toList.map fun entry => entry.2).mergeSort fun left right =>
    stateLE left.state right.state

/-- Solve every legal opening while sharing one transposition table. -/
def solveOpeningsM (gameSize : ℕ) : SolverM (List (ℕ × State)) := do
  let initialMask := fullMask gameSize
  let mut roots := []
  for (index, opening) in availableMoves gameSize initialMask do
    let root : State :=
      { remainingMask := eraseMove initialMask index
        deficit := opening
        toMove := .p2 }
    let _ ← solveAux gameSize (gameSize + 1) root
    roots := (opening, root) :: roots
  return roots.reverse

/-- Export the complete solved graph reachable after every legal opening. -/
def solveGame (gameSize : ℕ) : Except String SolverOutput :=
  match (solveOpeningsM gameSize).run {} with
  | .error message => .error message
  | .ok (openingRoots, cache) =>
      .ok ⟨gameSize, openingRoots, sortedNodes cache⟩

/- ## Independent list-based regression evaluator -/

/-- Independent normalized recurrence using a list rather than a bitmask and cache. -/
def referenceValue (remaining : List ℕ) (deficit : ℕ) : Outcome :=
  if remaining = [] then
    if deficit = 0 then .draw else .loss
  else if remaining.sum < deficit then
    .loss
  else
    let outcomes := remaining.attach.map fun ⟨counter, _⟩ =>
      let remaining' := remaining.erase counter
      if counter < deficit then
        referenceValue remaining' (deficit - counter)
      else
        (referenceValue remaining' (counter - deficit)).neg
    Outcome.best outcomes
termination_by remaining.length
decreasing_by
  all_goals
    have h := List.length_erase_add_one ‹_›
    omega

/-- Convert a mask state to its ascending list of remaining counters. -/
def remainingCounters (gameSize : ℕ) (state : State) : List ℕ :=
  (availableMoves gameSize state.remainingMask).map fun move => move.2

/-- Independently reconstruct the expected complete move list at a nonterminal state. -/
def referenceMoves (gameSize : ℕ) (state : State) : List MoveEvaluation :=
  (availableMoves gameSize state.remainingMask).map fun move =>
    let index := move.1
    let counter := move.2
    let continues := counter < state.deficit
    let child : State :=
      { remainingMask := state.remainingMask - Nat.shiftLeft 1 index
        deficit := if continues then state.deficit - counter else counter - state.deficit
        toMove := if continues then state.toMove else state.toMove.other }
    let childOutcome := referenceValue (remainingCounters gameSize child) child.deficit
    let outcome := if continues then childOutcome else childOutcome.neg
    ⟨counter, child, outcome⟩

/-- Check one solved node against the list recurrence and complete-edge contract. -/
def nodeAgreesWithReference (gameSize : ℕ) (node : SolvedNode) : Bool :=
  let remaining := remainingCounters gameSize node.state
  let expectedOutcome := referenceValue remaining node.state.deficit
  let expectedMoves :=
    if remaining = [] ∨ remaining.sum < node.state.deficit then []
    else referenceMoves gameSize node.state
  decide (node.outcome = expectedOutcome) && decide (node.moves = expectedMoves)

/-- Check that every child referenced by the solved graph is itself exported. -/
def containsEveryChild (output : SolverOutput) : Bool :=
  output.nodes.all fun node => node.moves.all fun move =>
    output.nodes.any fun candidate => decide (candidate.state = move.child)

/-- Check state uniqueness, edge closure, and list-reference agreement for a complete output. -/
def outputAgreesWithReference (output : SolverOutput) : Bool :=
  decide ((output.nodes.map fun node => node.state).Nodup) &&
    containsEveryChild output &&
    output.nodes.all (nodeAgreesWithReference output.gameSize)

/-- Run complete-output regression checks for every positive game size through `maxGameSize`. -/
def referenceAgreesThrough (maxGameSize : ℕ) : Bool :=
  (List.range maxGameSize).all fun offset =>
    match solveGame (offset + 1) with
    | .error _ => false
    | .ok output => outputAgreesWithReference output

/- ## Executable report -/

/-- Find one exported node by its exact normalized state. -/
def findNode? (output : SolverOutput) (state : State) : Option SolvedNode :=
  output.nodes.find? fun node => decide (node.state = state)

/-- Compute the original game's value from all exported post-opening roots. -/
def gameOutcome? (output : SolverOutput) : Option Outcome :=
  if output.gameSize = 0 then
    some .draw
  else
    let outcomes := output.openingRoots.filterMap fun openingRoot =>
      (findNode? output openingRoot.2).map fun node => node.outcome.neg
    if outcomes.length = output.openingRoots.length then some (Outcome.best outcomes) else none

/-- Count every retained legal edge in a complete solved graph. -/
def edgeCount (output : SolverOutput) : ℕ :=
  output.nodes.foldl (fun count node => count + node.moves.length) 0

def outcomeName : Outcome → String
  | .win => "win"
  | .loss => "loss"
  | .draw => "draw"

def run : IO Unit := do
  if !referenceAgreesThrough 8 then
    throw <| IO.userError "The normalized exact solver failed its complete-output regression."
  IO.println "Complete normalized outputs agree with the list recurrence through N=8."
  for gameSize in [3, 4, 7, 8] do
    match solveGame gameSize with
    | .error message => throw <| IO.userError message
    | .ok output =>
        match gameOutcome? output with
        | none => throw <| IO.userError s!"A root node is missing for N={gameSize}."
        | some outcome =>
            let summary := s!"N={gameSize}: {outcomeName outcome}; " ++
              s!"nodes={output.nodes.length}; edges={edgeCount output}"
            IO.println summary

end CatchUpSearch.ExactSolver
