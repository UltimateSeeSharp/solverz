/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CertificateChecker.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.StrategyContract

/-!
# Independent Catch-Up strategy-certificate checker

This module checks a `CatchUpSearch.StrategyDAG` without importing the exact solver or strategy
extractor. It decodes each bitmask state into the formal `CatchUp.GamePosition` API and
independently checks state bounds, terminal safety, legal moves, transition targets, child
coverage, uniqueness, and strict progress.

The boolean checker is not itself a proof of `CatchUp.CanAvoidLoss`. Its validity proposition is
designed for a separate soundness proof.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateChecker

open CatchUp

/-- Decode the set bits below `gameSize` as their represented counters, in ascending order. -/
def availableCounters (gameSize : ℕ) (state : State) : List ℕ :=
  (List.range gameSize).filterMap fun index =>
    if state.remainingMask.testBit index then some (index + 1) else none

/-- Decode a certificate state into the proof-level absolute game position. -/
def toGamePosition (gameSize : ℕ) (state : State) : GamePosition :=
  { remaining := (availableCounters gameSize state).toFinset
    deficit := state.deficit
    toMove := state.toMove }

/-- A mask is bounded when it has no set bit at or above `gameSize`. -/
def ValidState (gameSize : ℕ) (state : State) : Prop :=
  state.remainingMask < Nat.shiftLeft 1 gameSize

instance (gameSize : ℕ) (state : State) : Decidable (ValidState gameSize state) := by
  unfold ValidState
  infer_instance

/-- Whether a decoded state is terminal according to the formal Catch-Up rules. -/
def IsTerminalState (gameSize : ℕ) (state : State) : Prop :=
  (toGamePosition gameSize state).IsTerminal

instance (gameSize : ℕ) (state : State) : Decidable (IsTerminalState gameSize state) := by
  unfold IsTerminalState
  infer_instance

/-- Whether a decoded terminal state avoids a loss for one fixed player. -/
def TerminalSafeFor (gameSize : ℕ) (player : Player) (state : State) : Prop :=
  (toGamePosition gameSize state).terminalOutcomeFor player ≠ .loss

instance (gameSize : ℕ) (player : Player) (state : State) :
    Decidable (TerminalSafeFor gameSize player state) := by
  unfold TerminalSafeFor
  infer_instance

/-- Checker-local decidable wrapper around formal Catch-Up move legality. -/
def LegalMove (position : GamePosition) (counter : ℕ) : Prop :=
  position.LegalMove counter

instance (position : GamePosition) (counter : ℕ) : Decidable (LegalMove position counter) := by
  unfold LegalMove GamePosition.LegalMove
  infer_instance

/-- Whether the DAG contains one exact encoded state. -/
def ContainsState (dag : StrategyDAG) (state : State) : Prop :=
  state ∈ dag.nodes.map fun node => node.state

instance (dag : StrategyDAG) (state : State) : Decidable (ContainsState dag state) := by
  unfold ContainsState
  infer_instance

/-- Whether some DAG node decodes to a given proof-level game position. -/
def ContainsPosition (dag : StrategyDAG) (position : GamePosition) : Prop :=
  position ∈ dag.nodes.map fun node => toGamePosition dag.gameSize node.state

instance (dag : StrategyDAG) (position : GamePosition) :
    Decidable (ContainsPosition dag position) := by
  unfold ContainsPosition
  infer_instance

/-- Whether the DAG contains the strictly smaller formal position after one move. -/
def CoversMove (dag : StrategyDAG) (position : GamePosition) (counter : ℕ) : Prop :=
  ContainsPosition dag (position.afterPick counter) ∧
    (position.afterPick counter).remaining.card < position.remaining.card

instance (dag : StrategyDAG) (position : GamePosition) (counter : ℕ) :
    Decidable (CoversMove dag position counter) := by
  unfold CoversMove
  infer_instance

/-- The independent local validity condition for one certificate node. -/
def NodeValid (dag : StrategyDAG) (node : StrategyNode) : Prop :=
  ValidState dag.gameSize node.state ∧
    let position := toGamePosition dag.gameSize node.state
    match node.branch with
    | .terminal =>
        IsTerminalState dag.gameSize node.state ∧
          TerminalSafeFor dag.gameSize dag.player node.state
    | .owner counter =>
        ¬IsTerminalState dag.gameSize node.state ∧
          position.toMove = dag.player ∧
          LegalMove position counter ∧
          CoversMove dag position counter
    | .opponent counters =>
        ¬IsTerminalState dag.gameSize node.state ∧
          position.toMove ≠ dag.player ∧
          counters = availableCounters dag.gameSize node.state ∧
          counters.Forall fun counter =>
            LegalMove position counter ∧ CoversMove dag position counter

instance (dag : StrategyDAG) (node : StrategyNode) : Decidable (NodeValid dag node) := by
  unfold NodeValid
  cases node.branch <;> dsimp <;> infer_instance

/-- Global validity of a finite one-sided strategy certificate. -/
def DAGValid (dag : StrategyDAG) : Prop :=
  ContainsState dag dag.root ∧
    (dag.nodes.map fun node => node.state).Nodup ∧
    dag.nodes.Forall fun node => NodeValid dag node

instance (dag : StrategyDAG) : Decidable (DAGValid dag) := by
  unfold DAGValid
  infer_instance

/-- Independently check every obligation in a finite one-sided strategy certificate. -/
def checkCertificate (dag : StrategyDAG) : Bool :=
  decide (DAGValid dag)

end CatchUpSearch.CertificateChecker
