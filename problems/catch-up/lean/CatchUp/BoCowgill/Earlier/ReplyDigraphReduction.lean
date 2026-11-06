/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/ReplyDigraphReduction.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DrawOpening
public import CatchUp.BoCowgill.PairDeletion
public import CatchUp.BoCowgill.Earlier.TopFourClassification

/-!
# A ranked reply digraph for Catch-Up openings

This module packages the outcome of the first two distinct picks as a directed graph.
A directed edge from `a` to `b` says that `b` is a winning reply to opening `a`, while a neutral
pair says that the same two-pick continuation is drawn.  The final theorem uses a decreasing
natural-valued rank to rule out outgoing reply edges at a minimum-rank opening.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp

/-- The post-opening player can actually play from opening `a` and can still catch up. -/
def OpeningCatchable (S : Finset ℕ) (a : ℕ) : Prop :=
  S.erase a ≠ ∅ ∧ ¬ (S.erase a).sum (fun x ↦ x) < a

/-- A directed edge `a → b` means that `b` is a winning reply to opening `a`. -/
def ReplyEdge (S : Finset ℕ) (a b : ℕ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ (afterOpening S a).moveOutcome b = .win

/-- Two distinct available openings form a neutral pair when their two-pick outcome is a draw. -/
def NeutralPair (S : Finset ℕ) (a b : ℕ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ (afterOpening S a).moveOutcome b = .draw

/-- Every available first move leaves a drawn normalized game. -/
def EveryOpeningDraw (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, (afterOpening S a).value = .draw

/-- Every unordered pair of distinct counters has a drawn two-pick outcome. -/
def EveryPairNeutral (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → NeutralPair S a b

private theorem Outcome.best_eq_win_iff (outcomes : List Outcome) :
    Outcome.best outcomes = .win ↔ ∃ outcome ∈ outcomes, outcome = .win := by
  rw [← not_iff_not]
  simp
  constructor
  · intro hall hmem
    exact hall .win hmem rfl
  · intro hnot outcome hmem heq
    subst outcome
    exact hnot hmem

private theorem Outcome.best_eq_loss_iff (outcomes : List Outcome) :
    Outcome.best outcomes = .loss ↔ ∀ outcome ∈ outcomes, outcome = .loss := by
  rw [← not_iff_not]
  simp

/-- A reply edge in one direction is exactly a losing two-pick outcome in the reverse direction. -/
theorem reply_edge_iff_reverse_loss (S : Finset ℕ) {a b : ℕ} :
    ReplyEdge S a b ↔
      a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ (afterOpening S b).moveOutcome a = .loss := by
  constructor
  · rintro ⟨ha, hb, hab, hedge⟩
    refine ⟨ha, hb, hab, ?_⟩
    have hpair := move_outcome_after_opening_comm S hab
    rw [hedge] at hpair
    cases hreverse : (afterOpening S b).moveOutcome a <;>
      simp [hreverse, Outcome.neg] at hpair ⊢
  · rintro ⟨ha, hb, hab, hreverse⟩
    refine ⟨ha, hb, hab, ?_⟩
    rw [move_outcome_after_opening_comm S hab, hreverse]
    rfl

/-- Neutrality of a pair is symmetric. -/
theorem neutral_pair_comm (S : Finset ℕ) {a b : ℕ} :
    NeutralPair S a b ↔ NeutralPair S b a := by
  constructor
  · rintro ⟨ha, hb, hab, hneutral⟩
    refine ⟨hb, ha, Ne.symm hab, ?_⟩
    have hpair := move_outcome_after_opening_comm S hab
    rw [hneutral] at hpair
    cases hreverse : (afterOpening S b).moveOutcome a <;>
      simp [hreverse, Outcome.neg] at hpair ⊢
  · rintro ⟨hb, ha, hba, hneutral⟩
    refine ⟨ha, hb, Ne.symm hba, ?_⟩
    have hpair := move_outcome_after_opening_comm S hba
    rw [hneutral] at hpair
    cases hreverse : (afterOpening S a).moveOutcome b <;>
      simp [hreverse, Outcome.neg] at hpair ⊢

/-- Below a common larger opening `c`, the cross-picks `a < b < c` produce the same move outcome.
The equality includes the perspective switch when the cross-pick catches the opening deficit. -/
theorem pair_deletion_move_outcome_cross (S : Finset ℕ) {a b c : ℕ}
    (hab : a < b) (hbc : b < c) :
    Position.moveOutcome ⟨(S.erase a).erase c, c - a⟩ b =
      Position.moveOutcome ⟨(S.erase b).erase c, c - b⟩ a := by
  have hsame : b < c - a ↔ a < c - b := by omega
  by_cases hcontinue : b < c - a
  · have hcontinue' : a < c - b := hsame.mp hcontinue
    have hposition :
        (⟨(S.erase a).erase c, c - a⟩ : Position).afterPick b =
          (⟨(S.erase b).erase c, c - b⟩ : Position).afterPick a := by
      simp only [Position.afterPick, hcontinue, hcontinue', ite_true]
      congr 1
      · ext x
        simp only [Finset.mem_erase]
        aesop
      · omega
    simpa only [Position.moveOutcome, hcontinue, hcontinue', ite_true] using
      congrArg Position.value hposition
  · have hcontinue' : ¬ a < c - b := by simpa only [hsame] using hcontinue
    have hposition :
        (⟨(S.erase a).erase c, c - a⟩ : Position).afterPick b =
          (⟨(S.erase b).erase c, c - b⟩ : Position).afterPick a := by
      simp only [Position.afterPick, hcontinue, hcontinue', ite_false]
      congr 1
      · ext x
        simp only [Finset.mem_erase]
        aesop
      · omega
    simpa only [Position.moveOutcome, hcontinue, hcontinue', ite_false] using
      congrArg (fun position : Position ↦ position.value.neg) hposition

/-- Every unordered pair is oriented one way by a winning reply, or is neutral. -/
theorem reply_edge_or_neutral_pair_or_reverse (S : Finset ℕ) {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ReplyEdge S a b ∨ NeutralPair S a b ∨ ReplyEdge S b a := by
  cases hpair : (afterOpening S a).moveOutcome b with
  | win => exact Or.inl ⟨ha, hb, hab, hpair⟩
  | draw => exact Or.inr (Or.inl ⟨ha, hb, hab, hpair⟩)
  | loss =>
      right
      right
      exact (reply_edge_iff_reverse_loss S).mpr ⟨hb, ha, Ne.symm hab, hpair⟩

/-- At a catchable opening, winning is exactly the existence of an outgoing reply edge. -/
theorem after_opening_value_eq_win_iff_exists_reply_edge
    (S : Finset ℕ) {a : ℕ} (ha : a ∈ S) (hcatch : OpeningCatchable S a) :
    (afterOpening S a).value = .win ↔ ∃ b, ReplyEdge S a b := by
  rw [Position.value_eq_best_move_outcome (afterOpening S a) hcatch.1 hcatch.2,
    Outcome.best_eq_win_iff]
  constructor
  · rintro ⟨outcome, houtcome, hwin⟩
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp houtcome
    exact ⟨b, ha, Finset.mem_of_mem_erase hb, Ne.symm (Finset.ne_of_mem_erase hb),
      hwin⟩
  · rintro ⟨b, _, hb, hab, hwin⟩
    refine ⟨(afterOpening S a).moveOutcome b, ?_, hwin⟩
    apply List.mem_map.mpr
    exact ⟨⟨b, Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩⟩, by simp, rfl⟩

/-- At a catchable opening, losing means that every other vertex points into that opening. -/
theorem after_opening_value_eq_loss_iff_all_reverse_reply_edges
    (S : Finset ℕ) {a : ℕ} (ha : a ∈ S) (hcatch : OpeningCatchable S a) :
    (afterOpening S a).value = .loss ↔
      ∀ b ∈ S, b ≠ a → ReplyEdge S b a := by
  rw [Position.value_eq_best_move_outcome (afterOpening S a) hcatch.1 hcatch.2,
    Outcome.best_eq_loss_iff]
  constructor
  · intro hall b hb hba
    apply (reply_edge_iff_reverse_loss S).mpr
    refine ⟨hb, ha, hba, ?_⟩
    apply hall ((afterOpening S a).moveOutcome b)
    apply List.mem_map.mpr
    exact ⟨⟨b, Finset.mem_erase.mpr ⟨hba, hb⟩⟩, by simp, rfl⟩
  · intro hall outcome houtcome
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp houtcome
    have hedge := hall b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
    exact ((reply_edge_iff_reverse_loss S).mp hedge).2.2.2

/-- At a catchable opening, drawing means no outgoing winning reply and some neutral pair. -/
theorem after_opening_value_eq_draw_iff_no_reply_edge_and_neutral
    (S : Finset ℕ) {a : ℕ} (ha : a ∈ S) (hcatch : OpeningCatchable S a) :
    (afterOpening S a).value = .draw ↔
      (¬ ∃ b, ReplyEdge S a b) ∧ ∃ b, NeutralPair S a b := by
  constructor
  · intro hdraw
    have hnoedge : ¬ ∃ b, ReplyEdge S a b := by
      intro hedge
      have hwin := (after_opening_value_eq_win_iff_exists_reply_edge S ha hcatch).2 hedge
      rw [hdraw] at hwin
      cases hwin
    have hvalue : (afterOpening S a).value ≠ .loss := by simp [hdraw]
    rw [Position.value_eq_best_move_outcome (afterOpening S a) hcatch.1 hcatch.2,
      Outcome.best_ne_loss_iff] at hvalue
    obtain ⟨outcome, houtcome, hnloss⟩ := hvalue
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp houtcome
    have hbS := Finset.mem_of_mem_erase hb
    have hab := Finset.ne_of_mem_erase hb
    have hnwin : (afterOpening S a).moveOutcome b ≠ .win := by
      intro hwin
      exact hnoedge ⟨b, ha, hbS, Ne.symm hab, hwin⟩
    have hneutral : (afterOpening S a).moveOutcome b = .draw := by
      cases hmove : (afterOpening S a).moveOutcome b with
      | win => exact (hnwin hmove).elim
      | loss => exact (hnloss hmove).elim
      | draw => rfl
    exact ⟨hnoedge, b, ha, hbS, Ne.symm hab, hneutral⟩
  · rintro ⟨hnoedge, ⟨b, hneutral⟩⟩
    rw [Outcome.eq_draw_iff]
    constructor
    · rw [Position.value_eq_best_move_outcome (afterOpening S a) hcatch.1 hcatch.2,
        Outcome.best_ne_loss_iff]
      refine ⟨(afterOpening S a).moveOutcome b, ?_, ?_⟩
      · apply List.mem_map.mpr
        exact ⟨⟨b, Finset.mem_erase.mpr ⟨Ne.symm hneutral.2.2.1, hneutral.2.1⟩⟩,
          by simp, rfl⟩
      · simp [hneutral.2.2.2]
    · intro hwin
      exact hnoedge ((after_opening_value_eq_win_iff_exists_reply_edge S ha hcatch).1 hwin)

/-- When every opening is catchable, all openings are drawn exactly when all distinct pairs are
neutral. -/
theorem every_opening_draw_iff_every_pair_neutral
    (S : Finset ℕ) (hcatch : ∀ a ∈ S, OpeningCatchable S a) :
    EveryOpeningDraw S ↔ EveryPairNeutral S := by
  constructor
  · intro hopen a ha b hb hab
    have hnoA :=
      ((after_opening_value_eq_draw_iff_no_reply_edge_and_neutral S ha (hcatch a ha)).1
        (hopen a ha)).1
    have hnoB :=
      ((after_opening_value_eq_draw_iff_no_reply_edge_and_neutral S hb (hcatch b hb)).1
        (hopen b hb)).1
    rcases reply_edge_or_neutral_pair_or_reverse S ha hb hab with hedge | hneutral | hedge
    · exact (hnoA ⟨b, hedge⟩).elim
    · exact hneutral
    · exact (hnoB ⟨a, hedge⟩).elim
  · intro hpairs a ha
    apply (after_opening_value_eq_draw_iff_no_reply_edge_and_neutral S ha (hcatch a ha)).2
    constructor
    · rintro ⟨b, hedge⟩
      have hneutral := hpairs a ha b hedge.2.1 hedge.2.2.1
      have hwin := hedge.2.2.2
      rw [hneutral.2.2.2] at hwin
      cases hwin
    · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr (hcatch a ha).1
      exact ⟨b, hpairs a ha b (Finset.mem_of_mem_erase hb)
        (Ne.symm (Finset.ne_of_mem_erase hb))⟩

/-- If winning replies decrease a rank and every opening has a neutral partner, the game is drawn. -/
theorem value_eq_draw_of_ranked_reply_graph
    (S : Finset ℕ) (hS : S.Nonempty)
    (hcatch : ∀ a ∈ S, OpeningCatchable S a)
    (rank : ℕ → ℕ)
    (hrank : ∀ {a b}, ReplyEdge S a b → rank b < rank a)
    (hneutral : ∀ a ∈ S, ∃ b, NeutralPair S a b) :
    value S = .draw := by
  let ranks := S.image rank
  have hranks : ranks.Nonempty := hS.image rank
  let minimum := ranks.min' hranks
  have hminimum : minimum ∈ ranks := Finset.min'_mem ranks hranks
  obtain ⟨a, ha, hamin⟩ := Finset.mem_image.mp hminimum
  have hleast (b : ℕ) (hb : b ∈ S) : rank a ≤ rank b := by
    rw [hamin]
    exact Finset.min'_le ranks (rank b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
  apply (value_eq_draw_iff_exists_draw_after_opening S hS).2
  refine ⟨a, ha, ?_⟩
  apply (after_opening_value_eq_draw_iff_no_reply_edge_and_neutral S ha (hcatch a ha)).2
  constructor
  · rintro ⟨b, hedge⟩
    have hdecrease := hrank hedge
    have hbound := hleast b hedge.2.1
    omega
  · exact hneutral a ha

/-- Number-decreasing reply edges are the identity-rank instance of the ranked graph theorem. -/
theorem value_eq_draw_of_reply_edges_decrease_number
    (S : Finset ℕ) (hS : S.Nonempty)
    (hcatch : ∀ a ∈ S, OpeningCatchable S a)
    (hdecrease : ∀ {a b}, ReplyEdge S a b → b < a)
    (hneutral : ∀ a ∈ S, ∃ b, NeutralPair S a b) :
    value S = .draw := by
  exact value_eq_draw_of_ranked_reply_graph S hS hcatch id
    (by intro a b hedge; simpa using hdecrease hedge) hneutral

/-- Every interval opening is nonterminal and catchable once the interval has at least three
counters. -/
theorem opening_catchable_Icc (N a : ℕ) (hN : 3 ≤ N) (ha : a ∈ Finset.Icc 1 N) :
    OpeningCatchable (Finset.Icc 1 N) a := by
  constructor
  · by_cases haOne : a = 1
    · apply Finset.nonempty_iff_ne_empty.mp
      refine ⟨2, ?_⟩
      simp [haOne]
      omega

    · apply Finset.nonempty_iff_ne_empty.mp
      refine ⟨1, ?_⟩
      simp
      omega
  · intro hsum
    by_cases haTop : a = N
    · subst a
      have hsubset : {1, N - 1} ⊆ (Finset.Icc 1 N).erase N := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp
          omega
        · simp
          omega
      have hle := Finset.sum_le_sum_of_subset (f := fun x : ℕ ↦ x) hsubset
      have honeNe : 1 ≠ N - 1 := by omega
      have hle' : 1 + (N - 1) ≤
          ((Finset.Icc 1 N).erase N).sum (fun x ↦ x) := by
        simpa only [Finset.sum_pair honeNe] using hle
      omega
    · have htop : N ∈ (Finset.Icc 1 N).erase a := by
        simp
        omega
      have hle : N ≤ ((Finset.Icc 1 N).erase a).sum (fun x ↦ x) :=
        Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) htop
      have haLt : a < N := by
        have := (Finset.mem_Icc.mp ha).2
        omega
      omega

/-- For an interval with at least three counters, all openings are drawn exactly when all pairs
are neutral. -/
theorem every_opening_draw_Icc_iff_every_pair_neutral (N : ℕ) (hN : 3 ≤ N) :
    EveryOpeningDraw (Finset.Icc 1 N) ↔ EveryPairNeutral (Finset.Icc 1 N) := by
  exact every_opening_draw_iff_every_pair_neutral (Finset.Icc 1 N)
    (fun a ha ↦ opening_catchable_Icc N a hN ha)

/-- Pair-deletion nonloss above the diagonal forces every winning reply edge to decrease the
opening number. -/
theorem reply_edge_lt_of_all_pair_deletion_nonloss
    (N : ℕ)
    (hpairs : ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N, a < b →
      (pairDeletionPosition N a b).value ≠ .loss)
    {a b : ℕ} (hedge : ReplyEdge (Finset.Icc 1 N) a b) :
    b < a := by
  by_contra hba
  have hab : a < b := by
    have habLe : a ≤ b := Nat.le_of_not_gt hba
    exact lt_of_le_of_ne habLe hedge.2.2.1
  have hpair := hpairs a hedge.1 b hedge.2.1 hab
  have hmove := hedge.2.2.2
  simp only [Position.moveOutcome, afterOpening, Position.afterPick,
    not_lt_of_ge hab.le, ite_false] at hmove
  change (pairDeletionPosition N a b).value.neg = .win at hmove
  cases hvalue : (pairDeletionPosition N a b).value <;>
    simp [hvalue, Outcome.neg] at hmove hpair

/-- On an interval of length at least three, decreasing replies and neutral partners alone imply
the draw; catchability is automatic. -/
theorem value_Icc_eq_draw_of_reply_edges_decrease_number
    (N : ℕ) (hN : 3 ≤ N)
    (hdecrease : ∀ {a b}, ReplyEdge (Finset.Icc 1 N) a b → b < a)
    (hneutral : ∀ a ∈ Finset.Icc 1 N,
      ∃ b, NeutralPair (Finset.Icc 1 N) a b) :
    value (Finset.Icc 1 N) = .draw := by
  exact value_eq_draw_of_reply_edges_decrease_number (Finset.Icc 1 N)
    (Finset.nonempty_Icc.mpr (by omega))
    (fun a ha ↦ opening_catchable_Icc N a hN ha) hdecrease hneutral

/-- If winning replies decrease the opening number, a single neutral partner for the minimum
opening forces the interval draw. -/
theorem value_Icc_eq_draw_of_reply_edges_decrease_number_at_one
    (N : ℕ) (hN : 3 ≤ N)
    (hdecrease : ∀ {a b}, ReplyEdge (Finset.Icc 1 N) a b → b < a)
    (hneutralOne : ∃ b, NeutralPair (Finset.Icc 1 N) 1 b) :
    value (Finset.Icc 1 N) = .draw := by
  have hone : 1 ∈ Finset.Icc 1 N := by simp; omega
  apply (value_eq_draw_iff_exists_draw_after_opening (Finset.Icc 1 N)
    (Finset.nonempty_Icc.mpr (by omega))).2
  refine ⟨1, hone, ?_⟩
  apply (after_opening_value_eq_draw_iff_no_reply_edge_and_neutral
    (Finset.Icc 1 N) hone (opening_catchable_Icc N 1 hN hone)).2
  refine ⟨?_, hneutralOne⟩
  rintro ⟨b, hedge⟩
  have hlt : b < 1 := hdecrease hedge
  have hbLower : 1 ≤ b := (Finset.mem_Icc.mp hedge.2.1).1
  omega

/-- Pair-deletion nonloss above the diagonal plus one neutral pair at opening `1` implies the
interval draw. -/
theorem value_Icc_eq_draw_of_all_pair_deletion_nonloss_and_neutral_at_one
    (N : ℕ) (hN : 3 ≤ N)
    (hpairs : ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N, a < b →
      (pairDeletionPosition N a b).value ≠ .loss)
    (hneutralOne : ∃ b, NeutralPair (Finset.Icc 1 N) 1 b) :
    value (Finset.Icc 1 N) = .draw := by
  apply value_Icc_eq_draw_of_reply_edges_decrease_number_at_one N hN
  · exact reply_edge_lt_of_all_pair_deletion_nonloss N hpairs
  · exact hneutralOne

/-- Deleting the middle pair of four consecutive counters leaves a winning gap-three pair at
deficit one. -/
theorem top_four_middle_pair_residual_value_eq_win (a : ℕ) (ha : 3 ≤ a) :
    Position.value ⟨{a, a + 3}, 1⟩ = .win := by
  have h := CatchUpSearch.TopFourClassification.value_pair_exact
    a (a + 3) 1 (by omega) (by omega) (by omega)
  change Position.value ⟨{a, a + 3}, 1⟩ =
    (if 1 < (a + 3) - a then .win
      else if 1 = (a + 3) - a then .draw
      else if 1 ≤ a then .loss
      else if 1 < a + (a + 3) then .win
      else if 1 = a + (a + 3) then .draw
      else .loss) at h
  simpa only [ite_eq_left (by omega : 1 < (a + 3) - a)] using h

/-- In a tied four-counter block, replying downward across the middle pair is winning. -/
theorem top_four_middle_reply_edge (a : ℕ) (ha : 3 ≤ a) :
    ReplyEdge {a, a + 1, a + 2, a + 3} (a + 2) (a + 1) := by
  refine ⟨by simp, by simp, by omega, ?_⟩
  simp only [afterOpening, Position.moveOutcome, Position.afterPick,
    show a + 1 < a + 2 by omega, ite_true]
  have herase :
      (({a, a + 1, a + 2, a + 3} : Finset ℕ).erase (a + 2)).erase (a + 1) =
        {a, a + 3} := by
    ext x
    simp
    omega
  rw [herase, show a + 2 - (a + 1) = 1 by omega]
  exact top_four_middle_pair_residual_value_eq_win a ha

/-- The middle opening pair of a tied four-counter block is decisive, not neutral. -/
theorem top_four_middle_not_neutral (a : ℕ) (ha : 3 ≤ a) :
    ¬ NeutralPair {a, a + 1, a + 2, a + 3} (a + 1) (a + 2) := by
  intro hneutral
  have hreverse :=
    (neutral_pair_comm {a, a + 1, a + 2, a + 3}).mp hneutral
  have hedge := top_four_middle_reply_edge a ha
  have himpossible : Outcome.win = .draw := hedge.2.2.2.symm.trans hreverse.2.2.2
  exact Outcome.noConfusion himpossible

end CatchUp
