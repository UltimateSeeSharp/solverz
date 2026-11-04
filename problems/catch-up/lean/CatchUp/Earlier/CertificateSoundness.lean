/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CertificateSoundness.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.CertificateChecker

/-!
# Soundness of Catch-Up strategy certificates

This module proves that every strategy DAG accepted by the independent checker witnesses
`CatchUp.CanAvoidLoss` for the certificate owner at the decoded root position.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateChecker

open CatchUp

/-- Exact encoded-state containment implies containment of the decoded formal position. -/
theorem contains_position_of_contains_state (dag : StrategyDAG) (state : State)
    (hstate : ContainsState dag state) :
    ContainsPosition dag (toGamePosition dag.gameSize state) := by
  rw [ContainsState] at hstate
  rw [ContainsPosition]
  rcases List.mem_map.mp hstate with ⟨node, hnode, hnodeState⟩
  exact List.mem_map.mpr ⟨node, hnode, congrArg (toGamePosition dag.gameSize) hnodeState⟩

/-- Every node listed in a valid DAG satisfies its local branch obligations. -/
theorem node_valid_of_dag_valid {dag : StrategyDAG} (hvalid : DAGValid dag)
    {node : StrategyNode} (hnode : node ∈ dag.nodes) :
    NodeValid dag node := by
  unfold DAGValid at hvalid
  rw [List.forall_iff_forall_mem] at hvalid
  exact hvalid.2.2 node hnode

/-- Decoded legal moves are exactly the counters listed by the independent mask decoder. -/
theorem mem_available_counters_iff_legal_move (gameSize : ℕ) (state : State) (counter : ℕ) :
    counter ∈ availableCounters gameSize state ↔
      (toGamePosition gameSize state).LegalMove counter := by
  simp [toGamePosition, GamePosition.LegalMove]

/-- Every formal position represented in a valid strategy DAG is safe for the certificate owner. -/
theorem can_avoid_loss_of_contains_position (dag : StrategyDAG) (hvalid : DAGValid dag)
    (position : GamePosition) (hcontains : ContainsPosition dag position) :
    CanAvoidLoss dag.player position := by
  rw [ContainsPosition] at hcontains
  rcases List.mem_map.mp hcontains with ⟨node, hnode, hposition⟩
  have hnodeValid := node_valid_of_dag_valid hvalid hnode
  subst position
  cases hbranch : node.branch with
  | terminal =>
      simp only [NodeValid, hbranch] at hnodeValid
      rcases hnodeValid with ⟨_, hterminal, hsafe⟩
      apply (can_avoid_loss_iff_terminal_outcome_ne_loss dag.player
        (toGamePosition dag.gameSize node.state) hterminal).2
      exact hsafe
  | owner counter =>
      simp only [NodeValid, hbranch] at hnodeValid
      rcases hnodeValid with ⟨_, hterminal, htoMove, hlegal, hcovered⟩
      apply (can_avoid_loss_iff_exists_safe_move dag.player
        (toGamePosition dag.gameSize node.state) hterminal htoMove).2
      refine ⟨counter, hlegal, ?_⟩
      rcases hcovered with ⟨hchild, hprogress⟩
      exact can_avoid_loss_of_contains_position dag hvalid _ hchild
  | opponent counters =>
      simp only [NodeValid, hbranch] at hnodeValid
      rcases hnodeValid with ⟨_, hterminal, htoMove, hcounters, hforall⟩
      apply (can_avoid_loss_iff_forall_safe_moves dag.player
        (toGamePosition dag.gameSize node.state) hterminal htoMove).2
      intro counter hlegal
      have hcounterAvailable : counter ∈ availableCounters dag.gameSize node.state :=
        (mem_available_counters_iff_legal_move dag.gameSize node.state counter).2 hlegal
      have hcounter : counter ∈ counters := by
        simpa [hcounters] using hcounterAvailable
      have hmove := (List.forall_iff_forall_mem.mp hforall) counter hcounter
      rcases hmove.2 with ⟨hchild, hprogress⟩
      exact can_avoid_loss_of_contains_position dag hvalid _ hchild
termination_by position.remaining.card
decreasing_by
  all_goals simpa only [← hposition] using hprogress

/-- Every certificate accepted by the independent checker proves one-sided non-loss at its root. -/
theorem check_certificate_sound (dag : StrategyDAG) (hcheck : checkCertificate dag = true) :
    CanAvoidLoss dag.player (toGamePosition dag.gameSize dag.root) := by
  have hvalid : DAGValid dag :=
    of_decide_eq_true (by simpa [checkCertificate] using hcheck)
  apply can_avoid_loss_of_contains_position dag hvalid
  apply contains_position_of_contains_state
  exact hvalid.1

end CatchUpSearch.CertificateChecker
