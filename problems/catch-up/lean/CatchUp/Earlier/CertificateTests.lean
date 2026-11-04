/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CertificateTests.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.CertificateSoundness
public import CatchUp.Earlier.StrategyExtraction

/-!
# Catch-Up strategy-certificate regressions

This module contains small transparent certificates checked in the Lean kernel and executable
regressions connecting the exact solver, strategy extractor, independent checker, and soundness
theorem.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateTests

open CatchUp

/- ## Transparent kernel-checked certificates -/

/-- A positive-deficit terminal state in which player 2 is unable to catch up. -/
def terminalRoot : State := ⟨0, 1, .p2⟩

/-- The one-node terminal certificate is safe for player 1. -/
def terminalDAG : StrategyDAG :=
  ⟨1, .p1, terminalRoot, [⟨terminalRoot, .terminal⟩]⟩

theorem terminal_certificate_checks :
    CertificateChecker.checkCertificate terminalDAG = true := by
  decide

theorem terminal_certificate_sound :
    CanAvoidLoss terminalDAG.player
      (CertificateChecker.toGamePosition terminalDAG.gameSize terminalDAG.root) :=
  CertificateChecker.check_certificate_sound terminalDAG terminal_certificate_checks

/-- A nonterminal state where player 2 can catch up by taking counter 2. -/
def ownerRoot : State := ⟨2, 1, .p2⟩

/-- After counter 2 is taken, player 1 is behind in a terminal state. -/
def ownerChild : State := ⟨0, 1, .p1⟩

/-- A two-node certificate exercising the strategy owner's existential branch. -/
def ownerDAG : StrategyDAG :=
  ⟨2, .p2, ownerRoot,
    [⟨ownerRoot, .owner 2⟩, ⟨ownerChild, .terminal⟩]⟩

theorem owner_certificate_checks :
    CertificateChecker.checkCertificate ownerDAG = true := by
  decide

theorem owner_certificate_sound :
    CanAvoidLoss ownerDAG.player
      (CertificateChecker.toGamePosition ownerDAG.gameSize ownerDAG.root) :=
  CertificateChecker.check_certificate_sound ownerDAG owner_certificate_checks

theorem owner_certificate_value_ne_loss :
    (CertificateChecker.toGamePosition ownerDAG.gameSize ownerDAG.root).toPosition.value ≠ .loss := by
  have hvalue := (can_avoid_loss_iff_value ownerDAG.player
    (CertificateChecker.toGamePosition ownerDAG.gameSize ownerDAG.root)).mp owner_certificate_sound
  simpa [ownerDAG, ownerRoot, CertificateChecker.toGamePosition] using hvalue

/-- A nonterminal state where player 2 has exactly counter 1 available. -/
def opponentRoot : State := ⟨1, 1, .p2⟩

/-- Taking counter 1 produces an empty tied state with player 1 to move. -/
def opponentChild : State := ⟨0, 0, .p1⟩

/-- A two-node certificate exercising complete coverage of an opponent branch. -/
def opponentDAG : StrategyDAG :=
  ⟨1, .p1, opponentRoot,
    [⟨opponentRoot, .opponent [1]⟩, ⟨opponentChild, .terminal⟩]⟩

theorem opponent_certificate_checks :
    CertificateChecker.checkCertificate opponentDAG = true := by
  decide

theorem opponent_certificate_sound :
    CanAvoidLoss opponentDAG.player
      (CertificateChecker.toGamePosition opponentDAG.gameSize opponentDAG.root) :=
  CertificateChecker.check_certificate_sound opponentDAG opponent_certificate_checks

theorem opponent_certificate_value_ne_win :
    (CertificateChecker.toGamePosition opponentDAG.gameSize opponentDAG.root).toPosition.value ≠
      .win := by
  have hvalue := (can_avoid_loss_iff_value opponentDAG.player
    (CertificateChecker.toGamePosition opponentDAG.gameSize opponentDAG.root)).mp
      opponent_certificate_sound
  simpa [opponentDAG, opponentRoot, CertificateChecker.toGamePosition] using hvalue

/- ## Executable regressions -/

/-- Check every successfully extracted one-sided strategy for one solved game. -/
def successfulExtractionsCheck (output : SolverOutput) : Bool :=
  output.openingRoots.all fun root =>
    [Player.p1, Player.p2].all fun player =>
      match StrategyExtraction.extract output player root.2 with
      | .error _ => true
      | .ok dag => CertificateChecker.checkCertificate dag

/-- Check the solver, extractor, and independent checker for every game through a bound. -/
def extractedCertificatesCheckThrough (maxGameSize : ℕ) : Bool :=
  (List.range maxGameSize).all fun offset =>
    match ExactSolver.solveGame (offset + 1) with
    | .error _ => false
    | .ok output =>
        ExactSolver.outputAgreesWithReference output &&
          StrategyExtraction.extractionAgreesForGame output &&
          successfulExtractionsCheck output

/-- Check that representative malformed certificates are all rejected. -/
def malformedCertificatesRejected : Bool :=
  let unsafeTerminal := { terminalDAG with player := .p2 }
  let duplicateOwner := { ownerDAG with
    nodes := ⟨ownerRoot, .owner 2⟩ :: ownerDAG.nodes }
  let incompleteOpponent := { opponentDAG with
    nodes := [⟨opponentRoot, .opponent []⟩, ⟨opponentChild, .terminal⟩] }
  let wrongOwnerChild : State := ⟨0, 0, .p1⟩
  let wrongTransition := { ownerDAG with
    nodes := [⟨ownerRoot, .owner 2⟩, ⟨wrongOwnerChild, .terminal⟩] }
  !CertificateChecker.checkCertificate unsafeTerminal &&
    !CertificateChecker.checkCertificate duplicateOwner &&
    !CertificateChecker.checkCertificate incompleteOpponent &&
    !CertificateChecker.checkCertificate wrongTransition

/-- Run all deterministic certificate regressions. -/
def run : IO Unit := do
  if !extractedCertificatesCheckThrough 8 then
    throw <| IO.userError "A small extracted certificate failed its independent regression."
  if !malformedCertificatesRejected then
    throw <| IO.userError "The independent checker accepted a malformed certificate."
  IO.println "All extracted certificates agree with independent checks through N=8."
  IO.println "Representative malformed certificates are rejected."

end CatchUpSearch.CertificateTests
