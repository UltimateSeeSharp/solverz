/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/PartialCertificateSoundness.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.CertificateSoundness
public import CatchUp.Earlier.PartialCertificateChecker

/-!
# Soundness of Catch-Up partial-strategy certificates

This module proves that a partial strategy DAG accepted by the independent checker witnesses
`CatchUp.CanAvoidLoss` whenever every recognized target leaf has a separate proof of safety.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateChecker

open CatchUp

/-- A target predicate is sound when every valid state it recognizes is safe for the DAG owner. -/
def TargetSound (target : TargetPredicate) (dag : StrategyDAG) : Prop :=
  ∀ state, ValidState dag.gameSize state → target state = true →
    CanAvoidLoss dag.player (toGamePosition dag.gameSize state)

/-- Every listed node in a valid partial DAG satisfies its partial local obligations. -/
theorem partial_node_valid_of_partial_dag_valid {target : TargetPredicate} {dag : StrategyDAG}
    (hvalid : PartialDAGValid target dag) {node : StrategyNode} (hnode : node ∈ dag.nodes) :
    PartialNodeValid target dag node := by
  unfold PartialDAGValid at hvalid
  rw [List.forall_iff_forall_mem] at hvalid
  exact hvalid.2.2 node hnode

/-- Every formal position represented in a sound partial strategy DAG is safe for its owner. -/
theorem can_avoid_loss_of_contains_position_partial (target : TargetPredicate) (dag : StrategyDAG)
    (htarget : TargetSound target dag) (hvalid : PartialDAGValid target dag)
    (position : GamePosition) (hcontains : ContainsPosition dag position) :
    CanAvoidLoss dag.player position := by
  rw [ContainsPosition] at hcontains
  rcases List.mem_map.mp hcontains with ⟨node, hnode, hposition⟩
  have hnodeValid := partial_node_valid_of_partial_dag_valid hvalid hnode
  subst position
  rcases hnodeValid with ⟨hstateValid, htargetNode | hordinaryNode⟩
  · exact htarget node.state hstateValid htargetNode.1
  · cases hbranch : node.branch with
    | terminal =>
        simp only [NodeValid, hbranch] at hordinaryNode
        rcases hordinaryNode with ⟨_, hterminal, hsafe⟩
        apply (can_avoid_loss_iff_terminal_outcome_ne_loss dag.player
          (toGamePosition dag.gameSize node.state) hterminal).2
        exact hsafe
    | owner counter =>
        simp only [NodeValid, hbranch] at hordinaryNode
        rcases hordinaryNode with ⟨_, hterminal, htoMove, hlegal, hcovered⟩
        apply (can_avoid_loss_iff_exists_safe_move dag.player
          (toGamePosition dag.gameSize node.state) hterminal htoMove).2
        refine ⟨counter, hlegal, ?_⟩
        rcases hcovered with ⟨hchild, hprogress⟩
        exact can_avoid_loss_of_contains_position_partial target dag htarget hvalid _ hchild
    | opponent counters =>
        simp only [NodeValid, hbranch] at hordinaryNode
        rcases hordinaryNode with ⟨_, hterminal, htoMove, hcounters, hforall⟩
        apply (can_avoid_loss_iff_forall_safe_moves dag.player
          (toGamePosition dag.gameSize node.state) hterminal htoMove).2
        intro counter hlegal
        have hcounterAvailable : counter ∈ availableCounters dag.gameSize node.state :=
          (mem_available_counters_iff_legal_move dag.gameSize node.state counter).2 hlegal
        have hcounter : counter ∈ counters := by
          simpa [hcounters] using hcounterAvailable
        have hmove := (List.forall_iff_forall_mem.mp hforall) counter hcounter
        rcases hmove.2 with ⟨hchild, hprogress⟩
        exact can_avoid_loss_of_contains_position_partial target dag htarget hvalid _ hchild
termination_by position.remaining.card
decreasing_by
  all_goals simpa only [← hposition] using hprogress

/-- Every encoded state contained in a sound partial strategy DAG is safe for its owner. -/
theorem can_avoid_loss_of_contains_state_partial (target : TargetPredicate) (dag : StrategyDAG)
    (htarget : TargetSound target dag) (hvalid : PartialDAGValid target dag) (state : State)
    (hcontains : ContainsState dag state) :
    CanAvoidLoss dag.player (toGamePosition dag.gameSize state) := by
  apply can_avoid_loss_of_contains_position_partial target dag htarget hvalid
  exact contains_position_of_contains_state dag state hcontains

/-- Every partial certificate accepted by the independent checker is safe at its decoded root. -/
theorem check_partial_certificate_sound (target : TargetPredicate) (dag : StrategyDAG)
    (htarget : TargetSound target dag) (hcheck : checkPartialCertificate target dag = true) :
    CanAvoidLoss dag.player (toGamePosition dag.gameSize dag.root) := by
  have hvalid : PartialDAGValid target dag :=
    of_decide_eq_true (by simpa [checkPartialCertificate] using hcheck)
  exact can_avoid_loss_of_contains_state_partial target dag htarget hvalid dag.root hvalid.1

end CatchUpSearch.CertificateChecker
