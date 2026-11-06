/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/PartialCertificateChecker.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.CertificateChecker

/-!
# Independent Catch-Up partial-strategy certificate checker

This module extends the independent strategy-DAG checker with proof-backed target leaves. A target
leaf is encoded with the existing `StrategyBranch.terminal` constructor, but the partial checker
accepts it only when a supplied Boolean predicate recognizes the state. A separate soundness theorem
requires a proof that every recognized valid state satisfies `CatchUp.CanAvoidLoss`.

The ordinary full-certificate checker and its certificate format are unchanged.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateChecker

/-- An executable predicate selecting states justified by a separate safety theorem. -/
abbrev TargetPredicate := State → Bool

/--
One node is valid in a partial certificate when it is either a recognized target leaf or satisfies
all obligations of the ordinary independent checker.
-/
def PartialNodeValid (target : TargetPredicate) (dag : StrategyDAG)
    (node : StrategyNode) : Prop :=
  ValidState dag.gameSize node.state ∧
    ((target node.state = true ∧ node.branch = .terminal) ∨ NodeValid dag node)

instance (target : TargetPredicate) (dag : StrategyDAG) (node : StrategyNode) :
    Decidable (PartialNodeValid target dag node) := by
  unfold PartialNodeValid
  infer_instance

/-- Global validity of a finite strategy DAG whose recognized target leaves may stop recursion. -/
def PartialDAGValid (target : TargetPredicate) (dag : StrategyDAG) : Prop :=
  ContainsState dag dag.root ∧
    (dag.nodes.map fun node => node.state).Nodup ∧
    dag.nodes.Forall fun node => PartialNodeValid target dag node

instance (target : TargetPredicate) (dag : StrategyDAG) :
    Decidable (PartialDAGValid target dag) := by
  unfold PartialDAGValid
  infer_instance

/-- Independently check every finite obligation in a partial strategy certificate. -/
def checkPartialCertificate (target : TargetPredicate) (dag : StrategyDAG) : Bool :=
  decide (PartialDAGValid target dag)

end CatchUpSearch.CertificateChecker
