/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/NearRepair.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.FourOrphan

/-!
# NearRepair

Adaptive repairs in the remaining finite parameter range, composed with the large-parameter theorem
to retain all opponent turns.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.NearRepair

open CatchUp.FourOrphan (beforeMate)
open CatchUp.FourOrphan (six_transition)
open CatchUp.FourOrphan (thirteen_transition)
open CatchUp.FourOrphan (upper_transition)

/-- The defender's actual decision after the three previously certified picks. -/
def reached (q : ℕ) : GamePosition :=
  (FourOrphan.start q).afterPicks [6,13,q+1]

private theorem reached_eq (q : ℕ) (hq : 42≤q) : reached q=beforeMate q := by
  simp only [reached,GamePosition.after_picks_cons,GamePosition.after_picks_nil,
    six_transition q hq,thirteen_transition q hq,upper_transition q hq]

/-- Eight small endpoint games, checked in the kernel through the existing evaluator. -/
theorem low_endpoint_draw (q : ℕ) (h42 : 42≤q) (h56 : q≤56) (he : q%2=0) :
    Position.value ⟨{7,10,18,21,40,41,q},57-q⟩ = .draw := by
  interval_cases q <;> try omega
  all_goals rw [←Position.eval_eq_value]
  all_goals decide +kernel

/-- Twenty six-counter endpoint games; no unbounded inference from these cases. -/
theorem middle_endpoint_nonwin (q : ℕ) (h58 : 58≤q) (h96 : q≤96) (he : q%2=0) :
    Position.value ⟨{7,11,18,20,40,q},98-q⟩ ≠ .win := by
  interval_cases q <;> try omega
  all_goals rw [←Position.eval_eq_value]
  all_goals decide +kernel

/-- In the low range, 11 and 20 stay below the deficit; 19 completes the turn. -/
theorem low_turn (q : ℕ) (h42 : 42≤q) (h56 : q≤56) :
    CompletedTurn (reached q) [11,20,19]
      ⟨⟨{7,10,18,21,40,41,q},57-q⟩,.p1⟩ := by
  rw [reached_eq q h42]
  have ht := completed_turn_of_preparation (beforeMate q) [11,20] 19
    (by decide +kernel) (by decide +kernel)
    (by intro x hx; simp [beforeMate] at hx ⊢; tauto)
    (by right; simp [beforeMate]; omega) (by simp [beforeMate]; omega)
  have he : (beforeMate q).remaining \ insert 19 [11,20].toFinset=
      {7,10,18,21,40,41,q} := by ext t; simp [beforeMate]; omega
  change CompletedTurn (beforeMate q) [11,20,19]
    ⟨⟨(beforeMate q).remaining \ insert 19 [11,20].toFinset,50-(q-7)⟩,.p1⟩ at ht
  simpa only [he,show 50-(q-7)=57-q by omega] using ht

/-- The middle-range preparation totals 50, and 41 completes the turn. -/
theorem middle_turn (q : ℕ) (h58 : 58≤q) (h96 : q≤96) :
    CompletedTurn (reached q) [10,19,21,41]
      ⟨⟨{7,11,18,20,40,q},98-q⟩,.p1⟩ := by
  rw [reached_eq q (by omega)]
  have ht := completed_turn_of_preparation (beforeMate q) [10,19,21] 41
    (by decide +kernel) (by decide +kernel)
    (by intro x hx; simp [beforeMate] at hx ⊢; tauto)
    (by right; simp [beforeMate]; omega) (by simp [beforeMate]; omega)
  have he : (beforeMate q).remaining \ insert 41 [10,19,21].toFinset=
      {7,11,18,20,40,q} := by ext t; simp [beforeMate]; omega
  change CompletedTurn (beforeMate q) [10,19,21,41]
    ⟨⟨(beforeMate q).remaining \ insert 41 [10,19,21].toFinset,91-(q-7)⟩,.p1⟩ at ht
  simpa only [he,show 91-(q-7)=98-q by omega] using ht

/-- The boundary needs preparation 90 rather than the far rule's preparation 91. -/
theorem boundary_turn : CompletedTurn (reached 98) [7,10,11,21,41,98]
    ⟨⟨{18,19,20,40},97⟩,.p1⟩ := by
  rw [reached_eq 98 (by omega)]
  have ht := completed_turn_of_preparation (beforeMate 98) [7,10,11,21,41] 98
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have he : completedTurnEndpoint (beforeMate 98) (insert 98 [7,10,11,21,41].toFinset)=
      ⟨⟨{18,19,20,40},97⟩,.p1⟩ := by decide +kernel
  simpa only [he, List.cons_append, List.nil_append] using ht

/-- Three finite-range responses followed by the already proved large-q response. -/
def response (q : ℕ) : List ℕ :=
  if q≤56 then [11,20,19]
  else if q≤96 then [10,19,21,41]
  else if q=98 then [7,10,11,21,41,q]
  else [10,40,41,q]

/-- Explicit remaining support and deficit after the selected completed turn. -/
def endpoint (q : ℕ) : GamePosition :=
  if q≤56 then ⟨⟨{7,10,18,21,40,41,q},57-q⟩,.p1⟩
  else if q≤96 then ⟨⟨{7,11,18,20,40,q},98-q⟩,.p1⟩
  else if q=98 then ⟨⟨{18,19,20,40},97⟩,.p1⟩
  else ⟨⟨{7,11,18,19,20,21},98⟩,.p1⟩

private theorem reached_mover (q : ℕ) (hq : 42≤q) : (reached q).toMove=.p2 := by
  rw [reached_eq q hq]
  rfl
private theorem endpoint_mover (q : ℕ) : (endpoint q).toMove=.p1 := by
  unfold endpoint
  split_ifs <;> rfl
/-- The explicit adaptive response is one legal completed defender turn. -/
theorem adaptive_turn (q : ℕ) (h42 : 42≤q) (he : q%2=0) :
    CompletedTurn (reached q) (response q) (endpoint q) := by
  by_cases h56 : q≤56
  · simpa only [response,endpoint,ite_eq_left h56] using low_turn q h42 h56
  · by_cases h96 : q≤96
    · simpa only [response,endpoint,ite_eq_right h56,ite_eq_left h96] using
        middle_turn q (by omega) h96
    · by_cases h98 : q=98
      · subst q
        simpa [response,endpoint] using boundary_turn
      · simpa only [response,endpoint,reached,ite_eq_right h56,ite_eq_right h96,ite_eq_right h98] using
          FourOrphan.uniform_far_turn q (by omega)
/-- The opponent cannot force a win from any selected endpoint. -/
theorem adaptive_endpoint_nonwin (q : ℕ) (h42 : 42≤q) (he : q%2=0) :
    (endpoint q).toPosition.value≠.win := by
  by_cases h56 : q≤56
  · simp [endpoint,h56,low_endpoint_draw q h42 h56 he]
  · by_cases h96 : q≤96
    · simpa only [endpoint,ite_eq_right h56,ite_eq_left h96] using
        middle_endpoint_nonwin q (by omega) h96 he
    · by_cases h98 : q=98
      · subst q
        have hd : Position.value ⟨{18,19,20,40},97⟩=.draw := WholeTurn.sum_draw _
        simp [endpoint,hd]
      · have hl : Position.value ⟨{7,11,18,19,20,21},98⟩=.loss := by
          rw [Position.value.eq_def]
          decide +kernel
        simp [endpoint,h56,h96,h98,hl]
/-- Endpoint safety includes all future choices under the reference semantics. -/
theorem adaptive_endpoint_safe (q : ℕ) (h42 : 42≤q) (he : q%2=0) :
    CanAvoidLoss .p2 (endpoint q) := by
  rw [can_avoid_loss_iff_value,ite_eq_right (by rw [endpoint_mover]; decide)]
  exact adaptive_endpoint_nonwin q h42 he
/-- Safety of the selected response includes every later opponent choice. -/
theorem adaptive_repair (q : ℕ) (h42 : 42≤q) (he : q%2=0) :
    CanAvoidLoss .p2 (reached q) := by
  exact (adaptive_turn q h42 he).can_avoid_loss_of_safe_endpoint
    (reached_mover q h42) (adaptive_endpoint_safe q h42 he)
/-- Every legal complete opponent reply retains the defender's guarantee. -/
theorem every_opponent_turn_safe (q : ℕ) (h42 : 42≤q) (he : q%2=0)
    {picks : List ℕ} {after : GamePosition}
    (turn : CompletedTurn (endpoint q) picks after) : CanAvoidLoss .p2 after := by
  exact turn.safe_endpoint_of_can_avoid_loss (by rw [endpoint_mover]; decide)
    (adaptive_endpoint_safe q h42 he)
/-- The reached node is non-losing for all even q>=42, with no remaining q gap. -/
theorem uniform_reached_nonloss (q : ℕ) (h42 : 42≤q) (he : q%2=0) :
    (reached q).toPosition.value≠.loss := by
  have hs := adaptive_repair q h42 he
  simpa only [can_avoid_loss_iff_value,ite_eq_left (reached_mover q h42)] using hs
/-- The identical non-loss statement in the frozen absolute-score semantics. -/
theorem uniform_reference_nonloss (q : ℕ) (h42 : 42≤q) (he : q%2=0) :
    valueAux {7,10,11,18,19,20,21,40,41,q} 0 (q-7) false≠.loss := by
  rw [←Position.value_eq_value_aux _ 0 (q-7) (by omega)]
  have hs := uniform_reached_nonloss q h42 he
  simpa only [reached_eq q h42, beforeMate, Nat.sub_zero] using hs

end CatchUp.NearRepair
