/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/FourOrphan.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates;
module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.ReserveTriangle

/-!
# FourOrphan

A certified failure of a proposed four-pair orphan invariant, plus a proved large-parameter
defensive repair.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.FourOrphan

open CatchUp.DeficitTwo (win_of_catch)

/-- One kernel-checked finite subproof, reused by the counterexample and every lift. -/
theorem critical_loss :
    Position.value ⟨{7,10,11,18,19,20,21,40},34⟩ = .loss := by
  rw [←Position.eval_eq_value]
  decide +kernel

/-- Orphan seven plus four canonical pairs, at deficit seven. -/
def critical : GamePosition :=
  ⟨⟨{7,10,11,18,19,20,21,40,41},7⟩,.p1⟩

/-- Taking forty-one forces a strict win against every subsequent opponent choice. -/
theorem critical_win : critical.toPosition.value = .win := by
  have he : critical.remaining.erase 41={7,10,11,18,19,20,21,40} := by decide +kernel
  apply win_of_catch _ _ 41 (by decide +kernel) (by decide +kernel)
  change ({7,10,11,18,19,20,21,40,41}:Finset ℕ).erase 41=_ at he
  rw [he]
  exact critical_loss

/-- The critical support satisfies every proposed four-pair geometric hypothesis. -/
theorem critical_support :
    critical.remaining=insert 7 (SevenPairTest.pairedCounters {10,18,20,40}) ∧
      ({10,18,20,40}:Finset ℕ).card=4 ∧
      (∀ b∈({10,18,20,40}:Finset ℕ),10≤b ∧ b%2=0) ∧
      12∉({10,18,20,40}:Finset ℕ) := by
  decide +kernel

/-- The pair-count lift of the equal-deficit orphan invariant is false. -/
theorem not_uniform_four_equal :
    ¬(∀ B : Finset ℕ, B.card=4 →
      (∀ b∈B,10≤b ∧ b%2=0) → 12∉B →
      ∀ z : ℕ, (z=6 ∨ z=7) →
        Position.value ⟨insert z (SevenPairTest.pairedCounters B),z⟩ ≠ .win) := by
  intro h
  have hh := h {10,18,20,40} critical_support.2.1 critical_support.2.2.1
    critical_support.2.2.2 7 (by omega)
  rw [←critical_support.1] at hh
  exact hh critical_win

/-- The same strict win under the frozen literal score evaluator. -/
theorem critical_reference_win :
    valueAux {7,10,11,18,19,20,21,40,41} 0 7 false = .win := by
  rw [←Position.value_eq_value_aux _ 0 7 (by omega)]
  exact critical_win

/-- The waiting defender cannot avoid loss once the critical reserve is reached. -/
theorem critical_defender_loses : ¬CanAvoidLoss .p2 critical := by
  intro h
  have hh := (can_avoid_loss_iff_value .p2 critical).mp h
  change critical.toPosition.value≠.win at hh
  exact hh critical_win

/-- The previous count-two theorem and the failed addition of two pairs. -/
theorem adding_two_pairs_breaks_equal :
    Position.value ⟨{7,10,11,18,19},7⟩ ≠ .win ∧ critical.toPosition.value=.win := by
  exact ⟨ReserveTriangle.orphan_two_equal 7 10 18 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega),critical_win⟩

/-- Five core pairs around the same triangle reserve, for every q>=42. -/
def start (q : ℕ) : GamePosition :=
  ⟨⟨{6,7,13,10,11,18,19,20,21,40,41,q,q+1},1⟩,.p1⟩

def afterSix (q : ℕ) : GamePosition :=
  ⟨⟨{7,13,10,11,18,19,20,21,40,41,q,q+1},5⟩,.p2⟩

def afterThirteen (q : ℕ) : GamePosition :=
  ⟨⟨{7,10,11,18,19,20,21,40,41,q,q+1},8⟩,.p1⟩

def beforeMate (q : ℕ) : GamePosition :=
  ⟨⟨{7,10,11,18,19,20,21,40,41,q},q-7⟩,.p2⟩

theorem six_transition (q : ℕ) (hq : 42≤q) :
    (start q).afterPick 6=afterSix q := by
  have he : ({6,7,13,10,11,18,19,20,21,40,41,q,q+1}:Finset ℕ).erase 6=
      {7,13,10,11,18,19,20,21,40,41,q,q+1} := by ext t; simp; omega
  simp [start,afterSix,GamePosition.afterPick,Position.afterPick,he,Player.other]

theorem thirteen_transition (q : ℕ) (hq : 42≤q) :
    (afterSix q).afterPick 13=afterThirteen q := by
  have he : ({7,13,10,11,18,19,20,21,40,41,q,q+1}:Finset ℕ).erase 13=
      {7,10,11,18,19,20,21,40,41,q,q+1} := by ext t; simp; omega
  simp [afterSix,afterThirteen,GamePosition.afterPick,Position.afterPick,he,Player.other]

theorem upper_transition (q : ℕ) (hq : 42≤q) :
    (afterThirteen q).afterPick (q+1)=beforeMate q := by
  have he : ({7,10,11,18,19,20,21,40,41,q,q+1}:Finset ℕ).erase (q+1)=
      {7,10,11,18,19,20,21,40,41,q} := by ext t; simp; omega
  simp [afterThirteen,beforeMate,GamePosition.afterPick,Position.afterPick,he,
    show ¬q+1<8 by omega,show q+1-8=q-7 by omega,Player.other]

private theorem mate_transition (q : ℕ) (hq : 42≤q) :
    (beforeMate q).afterPick q=critical := by
  have he : ({7,10,11,18,19,20,21,40,41,q}:Finset ℕ).erase q=
      {7,10,11,18,19,20,21,40,41} := by ext t; simp; omega
  simp [beforeMate,critical,GamePosition.afterPick,Position.afterPick,he,
    show ¬q<q-7 by omega,show q-(q-7)=7 by omega,Player.other]

/-- These are actual five-core-pair supports, with distinct positive counters. -/
theorem start_support (q : ℕ) (hq : 42≤q) (hqe : q%2=0) :
    (start q).remaining=
      insert 6 (insert 7 (insert 13 (SevenPairTest.pairedCounters {10,18,20,40,q}))) ∧
      ({10,18,20,40,q}:Finset ℕ).card=5 ∧
      (∀ b∈({10,18,20,40,q}:Finset ℕ),10≤b ∧ b%2=0) ∧
      12∉({10,18,20,40,q}:Finset ℕ) := by
  constructor
  · ext t
    simp [start,SevenPairTest.pairedCounters]
    omega
  constructor
  · have h10 : 10∉({18,20,40,q}:Finset ℕ) := by simp; omega
    have h18 : 18∉({20,40,q}:Finset ℕ) := by simp; omega
    have h20 : 20∉({40,q}:Finset ℕ) := by simp; omega
    have h40 : 40∉({q}:Finset ℕ) := by simp; omega
    simp only [Finset.card_insert_of_notMem h10,Finset.card_insert_of_notMem h18,
      Finset.card_insert_of_notMem h20,Finset.card_insert_of_notMem h40,Finset.card_singleton]
  constructor
  · intro b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> omega
  · simp; omega

open CatchUp.SevenPairTest (step_of_catcher)

/-- The old triangle response followed by ordinary mates reaches the false reserve. -/
theorem uniform_counterplay_legal (q : ℕ) (hq : 42≤q) :
    GamePosition.PickTrace (start q) [6,13,q+1,q] critical := by
  apply GamePosition.PickTrace.cons
  · apply step_of_catcher _ _ 6
    · simp [start,GamePosition.LegalMove]
    · simp [start]
    · change 1≤6
      decide +kernel
  · rw [six_transition q hq]
    apply GamePosition.PickTrace.cons
    · apply step_of_catcher _ _ 13
      · simp [afterSix,GamePosition.LegalMove]
      · simp [afterSix]
      · change 5≤13
        decide +kernel
    · rw [thirteen_transition q hq]
      apply GamePosition.PickTrace.cons
      · apply step_of_catcher _ _ (q+1)
        · simp [afterThirteen,GamePosition.LegalMove]
        · simp [afterThirteen]
        · change 8≤q+1
          omega
      · rw [upper_transition q hq]
        apply GamePosition.PickTrace.cons
        · apply step_of_catcher _ _ q
          · simp [beforeMate,GamePosition.LegalMove]
          · simp [beforeMate]
          · change q-7≤q
            omega
        · rw [mate_transition q hq]
          exact GamePosition.PickTrace.nil _

/-- The selected lower mate is losing at the reached decision, for all q>=42.
No claim is made that every earlier defender strategy loses at the root. -/
theorem uniform_mate_loses (q : ℕ) (hq : 42≤q) :
    let p := (start q).afterPicks [6,13,q+1]
    p.toMove=.p2 ∧ p.toPosition.moveOutcome q=.loss := by
  simp only [GamePosition.after_picks_cons,GamePosition.after_picks_nil,
    six_transition q hq,thirteen_transition q hq,upper_transition q hq]
  have he : (beforeMate q).toPosition.afterPick q=critical.toPosition :=
    congrArg GamePosition.toPosition (mate_transition q hq)
  constructor
  · rfl
  · simp only [Position.moveOutcome,
      show ¬q<(beforeMate q).deficit by change ¬q<q-7; omega,
      ite_false,he,critical_win,Outcome.neg]

/-- The replacement is one legal four-pick turn by the same defender. -/
theorem uniform_far_turn (q : ℕ) (hq : 100≤q) :
    CompletedTurn ((start q).afterPicks [6,13,q+1]) [10,40,41,q]
      ⟨⟨{7,11,18,19,20,21},98⟩,.p1⟩ := by
  have h42 : 42≤q := by omega
  simp only [GamePosition.after_picks_cons,GamePosition.after_picks_nil,
    six_transition q h42,thirteen_transition q h42,upper_transition q h42]
  have ht := completed_turn_of_preparation (beforeMate q) [10,40,41] q
    (by decide +kernel) (by simp; omega)
    (by intro x hx; simp [beforeMate] at hx ⊢; tauto)
    (by right; simp [beforeMate]; omega) (by simp [beforeMate]; omega)
  have he : (beforeMate q).remaining \ insert q [10,40,41].toFinset=
      {7,11,18,19,20,21} := by ext t; simp [beforeMate]; omega
  have hs : (insert q [10,40,41].toFinset).sum (fun x => x)=q+91 := by
    rw [Finset.sum_insert (by simp; omega)]
    norm_num
  have hh : completedTurnEndpoint (beforeMate q) (insert q [10,40,41].toFinset)=
      ⟨⟨{7,11,18,19,20,21},98⟩,.p1⟩ := by
    change (⟨⟨(beforeMate q).remaining \ insert q [10,40,41].toFinset,
      (insert q [10,40,41].toFinset).sum (fun x => x)-(q-7)⟩,.p1⟩:GamePosition)=_
    rw [he,hs,show q+91-(q-7)=98 by omega]
  rw [hh] at ht
  exact ht

/-- For q>=100 the repair wins outright: the waiting player has total96
against deficit98. The terminal comparison, not a game-tree evaluation, closes it. -/
theorem uniform_far_repair (q : ℕ) (hq : 100≤q) :
    ((start q).afterPicks [6,13,q+1]).toPosition.value=.win := by
  let p := (start q).afterPicks [6,13,q+1]
  have ho : p.toMove≠.p1 := by
    simp only [p,GamePosition.after_picks_cons,GamePosition.after_picks_nil,
      six_transition q (by omega),thirteen_transition q (by omega),upper_transition q (by omega)]
    change Player.p2≠Player.p1
    decide +kernel
  have hl : Position.value ⟨{7,11,18,19,20,21},98⟩=.loss := by
    rw [Position.value.eq_def]
    decide +kernel
  by_contra hn
  have hs : CanAvoidLoss .p1 p := by
    rw [can_avoid_loss_iff_value,ite_eq_right ho]
    exact hn
  have he := (uniform_far_turn q hq).safe_endpoint_of_can_avoid_loss ho hs
  rw [can_avoid_loss_iff_value,ite_eq_left rfl] at he
  exact he hl
end CatchUp.FourOrphan
