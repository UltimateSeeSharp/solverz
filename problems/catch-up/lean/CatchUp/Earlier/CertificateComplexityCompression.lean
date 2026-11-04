/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CertificateComplexityCompression.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); its `run_cmd` axiom audit dropped (solverz checks axioms with `#print axioms`).
-/
module

public import Mathlib
public import CatchUp.Earlier.DeficitWinningBound
public import CatchUp.Earlier.PartialCertificateSoundness

/-!
# A structural compression rule outside the full-DAG language

An available maximum equal to the protected mover's deficit guarantees nonloss.
This theorem-backed leaf performs no outcome lookup. It uses the existing partial
checker, so compressed node counts are not counts in the full-DAG model.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateComplexityCompression

open CatchUp CertificateChecker

/-- Recognize a protected turn whose deficit is an available maximum counter. -/
def maximumDeficitTarget (N : ℕ) (owner : Player) : TargetPredicate := fun state =>
  let p := toGamePosition N state
  decide (p.toMove = owner ∧ p.deficit ∈ p.remaining ∧ ∀ x ∈ p.remaining, x ≤ p.deficit)

/-- The compression rule is structural and sound independently of any solved table. -/
theorem maximum_deficit_target_sound (dag : StrategyDAG) :
    TargetSound (maximumDeficitTarget dag.gameSize dag.player) dag := by
  intro state _ htarget
  have h : (toGamePosition dag.gameSize state).toMove = dag.player ∧
      (toGamePosition dag.gameSize state).deficit ∈ (toGamePosition dag.gameSize state).remaining ∧
      ∀ x ∈ (toGamePosition dag.gameSize state).remaining,
        x ≤ (toGamePosition dag.gameSize state).deficit := by
    exact of_decide_eq_true htarget
  rw [can_avoid_loss_iff_value, ite_eq_left h.1]
  exact Position.value_ne_loss_of_deficit_is_max _ _ h.2.1 h.2.2

/-- The ordinary partial checker validates every branch and uses only the proved shortcut. -/
theorem compressed_certificate_sound (dag : StrategyDAG)
    (hcheck : checkPartialCertificate (maximumDeficitTarget dag.gameSize dag.player) dag = true) :
    CanAvoidLoss dag.player (toGamePosition dag.gameSize dag.root) :=
  check_partial_certificate_sound _ dag (maximum_deficit_target_sound dag) hcheck

end CatchUpSearch.CertificateComplexityCompression
