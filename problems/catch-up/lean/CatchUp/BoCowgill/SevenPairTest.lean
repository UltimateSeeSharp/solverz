/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/SevenPairTest.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); private declarations that other files use made public, since modules hide privates;
module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.BoCowgill.AnchorFive

/-!
# SevenPairTest

Adding two pairs breaks a previously successful recursive defense; includes exact counterplay and a
symbolic bad-mate family.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.SevenPairTest

open CatchUp.DeficitTwo (win_of_move)

/-- The union of pairs with supplied starts; parity and separation need hypotheses. -/
def pairedCounters (B : Finset ℕ) : Finset ℕ := B.biUnion fun b ↦ {b,b+1}

/-- The deficit-nine two-pair base case does not extend to four pairs.
Taking five continues the same player's turn into the prior winning quadruple. -/
theorem lifted_nine_win :
    Position.value ⟨{5,6,7,10,11,20,21,40,41},9⟩ = .win := by
  have hw : Position.value ⟨{6,7,10,11,20,21,40,41},4⟩ = .win :=
    (CanonicalFour.four_four_win_iff 6 10 20 40 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mpr ⟨rfl,rfl,rfl,rfl⟩
  have he : ({5,6,7,10,11,20,21,40,41} : Finset ℕ).erase 5 =
      {6,7,10,11,20,21,40,41} := by decide +kernel
  apply win_of_move _ _ 5 (by decide +kernel) (by decide +kernel)
  simpa [Position.moveOutcome,Position.afterPick,he] using hw

/-- The original two-pair theorem and the failed two-pair addition together. -/
theorem adding_two_pairs_breaks_nine :
    Position.value ⟨{5,6,7,10,11},9⟩ ≠ .win ∧
      Position.value ⟨{5,6,7,10,11,20,21,40,41},9⟩ = .win := by
  exact ⟨AnchorFour.five_two_pairs_nine 6 10 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega),lifted_nine_win⟩

/-- Thus the geometric deficit-nine family cannot be a pair-count-uniform invariant. -/
theorem not_uniform_nine : ¬ (∀ B : Finset ℕ,
    2 ≤ B.card → B.card%2=0 → (∀ b ∈ B, 6 ≤ b ∧ b%2=0) → 8 ∉ B →
    Position.value ⟨insert 5 (pairedCounters B),9⟩ ≠ .win) := by
  intro h
  have hh := h {6,10,20,40} (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have he : insert 5 (pairedCounters {6,10,20,40}) =
      ({5,6,7,10,11,20,21,40,41} : Finset ℕ) := by decide +kernel
  rw [he] at hh
  exact hh lifted_nine_win

/-- The critical value also holds under the literal absolute-score evaluator. -/
theorem lifted_nine_reference_win :
    valueAux {5,6,7,10,11,20,21,40,41} 0 9 false = .win := by
  rw [← Position.value_eq_value_aux _ 0 9 (by omega)]
  exact lifted_nine_win

/-- Seven canonical pairs, minimum four, omitting eight for every even q>=42. -/
def start (q : ℕ) : GamePosition :=
  ⟨⟨{4,5,6,7,10,11,12,13,20,21,40,41,q,q+1},3⟩,.p1⟩

def afterFirst (q : ℕ) : GamePosition :=
  ⟨⟨{4,5,6,7,10,11,12,13,20,21,40,41,q+1},q-3⟩,.p2⟩

def afterFour (q : ℕ) : GamePosition :=
  ⟨⟨{5,6,7,10,11,12,13,20,21,40,41,q+1},q-7⟩,.p2⟩

def afterReturn : GamePosition := ⟨⟨{5,6,7,10,11,12,13,20,21,40,41},8⟩,.p1⟩

def beforeBadMate : GamePosition := ⟨⟨{5,6,7,10,11,13,20,21,40,41},4⟩,.p2⟩

def critical : GamePosition := ⟨⟨{5,6,7,10,11,20,21,40,41},9⟩,.p1⟩

theorem first_transition (q : ℕ) (hq : 42 ≤ q) :
    (start q).afterPick q = afterFirst q := by
  have he : ({4,5,6,7,10,11,12,13,20,21,40,41,q,q+1} : Finset ℕ).erase q =
      {4,5,6,7,10,11,12,13,20,21,40,41,q+1} := by ext t; simp; omega
  simp [start,afterFirst,GamePosition.afterPick,Position.afterPick,he,
    show ¬q<3 by omega,Player.other]

theorem four_transition (q : ℕ) (hq : 42 ≤ q) :
    (afterFirst q).afterPick 4 = afterFour q := by
  have he : ({4,5,6,7,10,11,12,13,20,21,40,41,q+1} : Finset ℕ).erase 4 =
      {5,6,7,10,11,12,13,20,21,40,41,q+1} := by ext t; simp; omega
  simp [afterFirst,afterFour,GamePosition.afterPick,Position.afterPick,he,
    show 4<q-3 by omega,show q-3-4=q-7 by omega]

theorem return_transition (q : ℕ) (hq : 42 ≤ q) :
    (afterFour q).afterPick (q+1) = afterReturn := by
  have he : ({5,6,7,10,11,12,13,20,21,40,41,q+1} : Finset ℕ).erase (q+1) =
      {5,6,7,10,11,12,13,20,21,40,41} := by ext t; simp; omega
  simp [afterFour,afterReturn,GamePosition.afterPick,Position.afterPick,he,
    show ¬q+1<q-7 by omega,show q+1-(q-7)=8 by omega,Player.other]

/-- Legality is separate from the evaluator: an available catcher rules out
an early terminal state even when the chosen pick itself continues the turn. -/
theorem step_of_catcher (p : GamePosition) (x c : ℕ)
    (hx : p.LegalMove x) (hc : c ∈ p.remaining) (hd : p.deficit ≤ c) :
    p.Step (p.afterPick x) := by
  apply GamePosition.step_after_pick p x _ hx
  rw [GamePosition.not_is_terminal_iff]
  exact ⟨Finset.nonempty_iff_ne_empty.mp ⟨c,hc⟩,
    Nat.not_lt.mpr (hd.trans (Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hc))⟩

/-- The symbolic support really is seven distinct canonical pairs omitting eight. -/
theorem start_support (q : ℕ) (hq : 42 ≤ q) (hqe : q%2=0) :
    (start q).remaining = pairedCounters {4,6,10,12,20,40,q} ∧
      ({4,6,10,12,20,40,q} : Finset ℕ).card = 7 ∧
      (∀ b ∈ ({4,6,10,12,20,40,q} : Finset ℕ), 4 ≤ b ∧ b%2=0) ∧
      8 ∉ (start q).remaining := by
  constructor
  · ext t
    simp [start,pairedCounters]
    omega
  constructor
  · have he : ({4,6,10,12,20,40,q} : Finset ℕ) = insert q {4,6,10,12,20,40} := by
      ext t; simp; omega
    have hn : q ∉ ({4,6,10,12,20,40} : Finset ℕ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton]
      omega
    rw [he,Finset.card_insert_of_notMem hn]
    decide +kernel
  constructor
  · intro b hb
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    omega
  · change 8 ∉ ({4,5,6,7,10,11,12,13,20,21,40,41,q,q+1} : Finset ℕ)
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega

/-- The candidate's legal counterplay: the friendly choices are four, q+1,
and then the ordinary mate thirteen. The first two friendly picks share a turn. -/
theorem candidate_counterplay_legal (q : ℕ) (hq : 42 ≤ q) :
    GamePosition.PickTrace (start q) [q,4,q+1,12,13] critical := by
  apply GamePosition.PickTrace.cons
  · apply step_of_catcher _ _ q
    · simp [GamePosition.LegalMove,start]
    · simp [start]
    · change 3 ≤ q
      omega
  · rw [first_transition q hq]
    apply GamePosition.PickTrace.cons
    · apply step_of_catcher _ _ (q+1)
      · simp [GamePosition.LegalMove,afterFirst]
      · simp [afterFirst]
      · change q-3 ≤ q+1
        omega
    · rw [four_transition q hq]
      apply GamePosition.PickTrace.cons
      · apply step_of_catcher _ _ (q+1)
        · simp [GamePosition.LegalMove,afterFour]
        · simp [afterFour]
        · change q-7 ≤ q+1
          omega
      · rw [return_transition q hq]
        apply GamePosition.PickTrace.cons
        · apply step_of_catcher _ _ 12
          · unfold GamePosition.LegalMove
            decide +kernel
          · decide +kernel
          · decide +kernel
        · have he : afterReturn.afterPick 12 = beforeBadMate := by decide +kernel
          rw [he]
          apply GamePosition.PickTrace.cons
          · apply step_of_catcher _ _ 13
            · unfold GamePosition.LegalMove
              decide +kernel
            · decide +kernel
            · decide +kernel
          · have hf : beforeBadMate.afterPick 13 = critical := by decide +kernel
            rw [hf]
            exact GamePosition.PickTrace.nil _

/-- No defender strategy can recover after these particular proposed choices.
This is not a statement that the starting seven-pair position is lost. -/
theorem critical_defender_cannot_avoid_loss : ¬ CanAvoidLoss .p2 critical := by
  simp [can_avoid_loss_iff_value,critical,lifted_nine_win]

/-- The mate is a strictly losing move at the ten-counter decision node. -/
theorem ordinary_mate_loses : beforeBadMate.toPosition.moveOutcome 13 = .loss := by
  have he : ({5,6,7,10,11,13,20,21,40,41} : Finset ℕ).erase 13 =
      {5,6,7,10,11,20,21,40,41} := by decide +kernel
  simp [beforeBadMate,Position.moveOutcome,Position.afterPick,he,lifted_nine_win,
    Outcome.neg]

/-- The same losing decision node is reached for arbitrarily large seventh pairs. -/
theorem uniform_bad_mate (q : ℕ) (hq : 42 ≤ q) :
    ((start q).afterPicks [q,4,q+1,12]).toMove = .p2 ∧
      ((start q).afterPicks [q,4,q+1,12]).toPosition.moveOutcome 13 = .loss := by
  have he : afterReturn.afterPick 12 = beforeBadMate := by decide +kernel
  simp only [GamePosition.after_picks_cons,GamePosition.after_picks_nil,
    first_transition q hq,four_transition q hq,return_transition q hq,he]
  exact ⟨rfl,ordinary_mate_loses⟩

end CatchUp.SevenPairTest
