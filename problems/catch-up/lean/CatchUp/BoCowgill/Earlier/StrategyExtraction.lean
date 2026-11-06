/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/StrategyExtraction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.ExactSolver

/-!
# Catch-Up one-sided strategy extraction

This research module extracts a deterministic one-sided non-loss strategy DAG from the complete
solved graph produced by `CatchUp.Earlier.ExactSolver`. At the strategy owner's nodes it retains one
safe move; at the opponent's nodes it retains every legal move.

The extractor trusts the solved graph's annotations. Its output is therefore untrusted certificate
data, not a proof of `CatchUp.CanAvoidLoss`. A later independent checker will recompute legality,
transitions, terminal outcomes, and acyclic progress.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.StrategyExtraction

open CatchUp

/-- Whether a current-mover outcome avoids a loss for one fixed player. -/
def outcomeSafeFor (player : Player) (state : State) (outcome : Outcome) : Bool :=
  if state.toMove = player then decide (outcome ≠ .loss) else decide (outcome ≠ .win)

/--
Select the certificate branch at one solved node and return the moves that must be traversed.

This function checks the solver's annotations for internal consistency but is not the independent
certificate checker: in particular, it consumes the solver's precomputed child states and outcomes.
-/
def selectBranch (gameSize : ℕ) (player : Player) (node : SolvedNode) :
    Except String (StrategyBranch × List MoveEvaluation) := do
  if !outcomeSafeFor player node.state node.outcome then
    throw s!"state is losing for {repr player}: {repr node.state}"
  match ExactSolver.terminalOutcome? gameSize node.state with
  | some expectedOutcome =>
      if node.moves ≠ [] then
        throw s!"terminal node has outgoing moves: {repr node.state}"
      if node.outcome ≠ expectedOutcome then
        throw s!"terminal node has the wrong outcome: {repr node.state}"
      pure (.terminal, [])
  | none =>
      if node.moves = [] then
        throw s!"nonterminal node has no outgoing moves: {repr node.state}"
      if node.state.toMove = player then
        match node.moves.find? fun move => decide (move.outcome ≠ .loss) with
        | none => throw s!"owner has no non-losing move: {repr node.state}"
        | some move => pure (.owner move.counter, [move])
      else
        if node.moves.all fun move => decide (move.outcome ≠ .win) then
          pure (.opponent (node.moves.map fun move => move.counter), node.moves)
        else
          throw s!"opponent has a winning continuation: {repr node.state}"

/-- Strategy nodes accumulated while traversing the selected policy. -/
abbrev StrategyCache := Std.HashMap CacheKey StrategyNode

/-- Strategy extraction combines a visited-state cache with explicit failure. -/
abbrev ExtractionM := StateT StrategyCache (Except String)

/-- Traverse exactly the children required by a fixed player's one-sided policy. -/
def extractAux (output : SolverOutput) (player : Player) : ℕ → State → ExtractionM Unit
  | 0, state => do
      if (← get)[state.cacheKey]?.isSome then
        return ()
      throw s!"strategy extraction fuel exhausted at {repr state}"
  | fuel + 1, state => do
      if (← get)[state.cacheKey]?.isSome then
        return ()
      let solvedNode ←
        match ExactSolver.findNode? output state with
        | none => throw s!"solved graph is missing state {repr state}"
        | some node => pure node
      let (branch, followedMoves) ← selectBranch output.gameSize player solvedNode
      modify fun cache => cache.insert state.cacheKey ⟨state, branch⟩
      for move in followedMoves do
        extractAux output player fuel move.child

/-- Convert the visited-state cache to a deterministic node list. -/
def sortedStrategyNodes (cache : StrategyCache) : List StrategyNode :=
  (cache.toList.map fun entry => entry.2).mergeSort fun left right =>
    ExactSolver.stateLE left.state right.state

/-- Extract a deterministic one-sided non-loss strategy rooted at one solved state. -/
def extract (output : SolverOutput) (player : Player) (root : State) : Except String StrategyDAG :=
  match (extractAux output player (output.gameSize + 1) root).run {} with
  | .error message => .error message
  | .ok (_, cache) => .ok ⟨output.gameSize, player, root, sortedStrategyNodes cache⟩

/-- Extract a one-sided strategy from one of the interval game's post-opening roots. -/
def extractOpening (output : SolverOutput) (player : Player) (opening : ℕ) :
    Except String StrategyDAG :=
  match output.openingRoots.find? fun root => decide (root.1 = opening) with
  | none => .error s!"opening {opening} is absent from the solved output"
  | some root => extract output player root.2

/- ## Regression checks against the complete solved graph -/

/-- Whether a strategy DAG contains a given normalized state. -/
def containsState (dag : StrategyDAG) (state : State) : Bool :=
  dag.nodes.any fun node => decide (node.state = state)

/-- Check one extracted strategy node against the branch selected from its solved node. -/
def nodeAgreesWithSolvedGraph (output : SolverOutput) (dag : StrategyDAG)
    (node : StrategyNode) : Bool :=
  match ExactSolver.findNode? output node.state with
  | none => false
  | some solvedNode =>
      match selectBranch output.gameSize dag.player solvedNode with
      | .error _ => false
      | .ok (expectedBranch, followedMoves) =>
          decide (node.branch = expectedBranch) &&
            followedMoves.all fun move => containsState dag move.child

/-- Check the metadata, uniqueness, selected branches, and followed-child closure of an extraction. -/
def agreesWithSolvedGraph (output : SolverOutput) (dag : StrategyDAG) : Bool :=
  decide (dag.gameSize = output.gameSize) &&
    containsState dag dag.root &&
    decide ((dag.nodes.map fun node => node.state).Nodup) &&
    dag.nodes.all (nodeAgreesWithSolvedGraph output dag)

/-- Check that extraction succeeds exactly for a solved root that is safe for the fixed player. -/
def extractionMatchesSafety (output : SolverOutput) (player : Player) (root : State) : Bool :=
  match ExactSolver.findNode? output root with
  | none => false
  | some solvedNode =>
      match extract output player root with
      | .error _ => !outcomeSafeFor player root solvedNode.outcome
      | .ok dag =>
          outcomeSafeFor player root solvedNode.outcome && agreesWithSolvedGraph output dag

/-- Check extraction for both players at every post-opening root of one solved game. -/
def extractionAgreesForGame (output : SolverOutput) : Bool :=
  output.openingRoots.all fun root =>
    [Player.p1, Player.p2].all fun player => extractionMatchesSafety output player root.2

/-- Run extraction regressions for every positive interval-game size through `maxGameSize`. -/
def extractionAgreesThrough (maxGameSize : ℕ) : Bool :=
  (List.range maxGameSize).all fun offset =>
    match ExactSolver.solveGame (offset + 1) with
    | .error _ => false
    | .ok output => extractionAgreesForGame output

end CatchUpSearch.StrategyExtraction
