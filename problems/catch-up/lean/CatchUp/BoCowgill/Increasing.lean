/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Increasing.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Executable
public import CatchUp.BoCowgill.PairDeletion
public import CatchUp.BoCowgill.CompletedTurn
public import CatchUp.BoCowgill.ReachableBounds

/-!
# Increasing turns without restricting the opponent

Two picks that both lie below the original deficit commute, including player identities. This
makes consecutive least-safe picks strictly increasing. The executable reduction below imposes
that ordering only on the protected player's choices; all opponent replies remain available.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.Increasing

/-- A safe pick preserves nonloss for the actual player who is currently acting. -/
def SafePick (position : GamePosition) (x : ℕ) : Prop :=
  position.LegalMove x ∧ CanAvoidLoss position.toMove (position.afterPick x)

/-- Minimality refers to safe choices at this node, not merely to available counters. -/
def LeastSafePick (position : GamePosition) (x : ℕ) : Prop :=
  SafePick position x ∧ ∀ y, SafePick position y → x ≤ y

/-- Continuing a catchable turn cannot create an early terminal state. -/
theorem nonterminal_after_continue (position : GamePosition) (x : ℕ)
    (hn : ¬ position.IsTerminal) (hx : position.LegalMove x)
    (hd : x < position.deficit) : ¬ (position.afterPick x).IsTerminal := by
  exact position.after_pick_not_terminal_of_lt x hn hx hd

/-- Two raw picks below the original deficit commute even if the second one catches. -/
theorem after_pick_commute (position : GamePosition) (x y : ℕ)
    (hx : x < position.deficit) (hy : y < position.deficit) :
    (position.afterPick x).afterPick y = (position.afterPick y).afterPick x := by
  cases position with
  | mk p mover =>
    cases p with
    | mk remaining deficit =>
      dsimp at hx hy
      simp only [GamePosition.afterPick, Position.afterPick, hx, hy, ite_true]
      by_cases hsum : x + y < deficit
      · have hxy : y < deficit - x := by omega
        have hyx : x < deficit - y := by omega
        simp only [hxy, hyx, ite_true]
        rw [Finset.erase_right_comm]
        congr 2; omega
      · have hxy : ¬ y < deficit - x := by omega
        have hyx : ¬ x < deficit - y := by omega
        simp only [hxy, hyx, ite_false]
        rw [Finset.erase_right_comm]
        congr 2; omega

/-- Reordering two continuing first picks preserves the ability to choose the second one. -/
theorem safe_after_reordered_pick (position : GamePosition) (x y : ℕ)
    (hn : ¬ position.IsTerminal) (hx : position.LegalMove x)
    (hy : (position.afterPick x).LegalMove y)
    (hxd : x < position.deficit) (hyd : y < position.deficit)
    (hsafe : CanAvoidLoss position.toMove ((position.afterPick x).afterPick y)) :
    SafePick position y := by
  have hyR : y ∈ position.remaining := Finset.mem_of_mem_erase hy
  have hne : x ≠ y := (Finset.ne_of_mem_erase hy).symm
  refine ⟨hyR, ?_⟩
  apply (can_avoid_loss_iff_exists_safe_move position.toMove (position.afterPick y)
    (nonterminal_after_continue position y hn hyR hyd)
    (position.to_move_after_pick_of_lt y hyd)).mpr
  refine ⟨x, Finset.mem_erase.mpr ⟨hne, hx⟩, ?_⟩
  rw [← after_pick_commute position x y hxd hyd]
  exact hsafe

/-- After a least-safe continuing pick, every safe next pick is strictly larger. -/
theorem safe_next_gt (position : GamePosition) (x y : ℕ)
    (hn : ¬ position.IsTerminal) (hleast : LeastSafePick position x)
    (hcontinue : x < position.deficit)
    (hnext : SafePick (position.afterPick x) y) : x < y := by
  by_contra hnot
  have hyd : y < position.deficit := by omega
  have hsafe : CanAvoidLoss position.toMove ((position.afterPick x).afterPick y) := by
    simpa only [position.to_move_after_pick_of_lt x hcontinue] using hnext.2
  have hswap := safe_after_reordered_pick position x y hn hleast.1.1 hnext.1
    hcontinue hyd hsafe
  have hmin := hleast.2 y hswap
  have hne : y ≠ x := Finset.ne_of_mem_erase hnext.1
  omega

/-- A safe nonterminal state has a least-safe available pick. -/
theorem exists_least_safe (position : GamePosition) (hn : ¬ position.IsTerminal)
    (hsafe : CanAvoidLoss position.toMove position) : ∃ x, LeastSafePick position x := by
  classical
  obtain ⟨x, hx, hchild⟩ := (can_avoid_loss_iff_exists_safe_move position.toMove position hn rfl).mp
    hsafe
  let choices := position.remaining.filter (fun y ↦ CanAvoidLoss position.toMove
    (position.afterPick y))
  have hchoices : choices.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, hchild⟩⟩
  refine ⟨choices.min' hchoices, ?_⟩
  constructor
  · exact Finset.mem_filter.mp (Finset.min'_mem choices hchoices)
  · intro y hy
    exact Finset.min'_le choices y (Finset.mem_filter.mpr hy)

/-- The protected player's next pick must exceed `lower`; opponent picks are unrestricted. -/
def check (player : Player) (position : GamePosition) (lower : ℕ) : Bool :=
  if position.IsTerminal then
    decide (position.terminalOutcomeFor player ≠ .loss)
  else if position.toMove = player then
    position.remaining.attach.fold (· || ·) false fun counter ↦
      decide (lower < counter.1) && check player (position.afterPick counter.1) counter.1
  else
    position.remaining.attach.fold (· && ·) true fun counter ↦
      check player (position.afterPick counter.1) 0
termination_by position.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    exact counter.2

/-- Increasing choices certify ordinary nonloss against all legal opponent replies. -/
theorem check_sound (player : Player) (position : GamePosition) (lower : ℕ)
    (hcheck : check player position lower = true) : CanAvoidLoss player position := by
  rw [check.eq_def] at hcheck
  by_cases hn : position.IsTerminal
  · apply (can_avoid_loss_iff_terminal_outcome_ne_loss player position hn).mpr
    simpa [hn] using hcheck
  · by_cases hm : position.toMove = player
    · rw [ite_eq_right hn, ite_eq_left hm] at hcheck
      rw [Finset.fold_op_rel_iff_or (r := fun _ value : Bool ↦ value = true) (c := true)
        (by simp)] at hcheck
      simp only [Bool.false_eq_true, false_or, Finset.mem_attach, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck
      obtain ⟨⟨x, hx⟩, _, _, hchild⟩ := hcheck
      apply (can_avoid_loss_iff_exists_safe_move player position hn hm).mpr
      exact ⟨x, hx, check_sound player (position.afterPick x) x hchild⟩
    · rw [ite_eq_right hn, ite_eq_right hm] at hcheck
      rw [Finset.fold_op_rel_iff_and (r := fun _ value : Bool ↦ value = true) (c := true)
        (by simp)] at hcheck
      simp only [true_and, Finset.mem_attach] at hcheck
      apply (can_avoid_loss_iff_forall_safe_moves player position hn hm).mpr
      intro x hx
      exact check_sound player (position.afterPick x) 0 (hcheck ⟨x, hx⟩ True.intro)
termination_by position.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    assumption

/-- Completeness uses a structural bound on safe choices, propagated by least-safe commutation. -/
theorem check_complete (player : Player) (position : GamePosition) (lower : ℕ)
    (hpositive : ∀ x ∈ position.remaining, 0 < x)
    (hsafe : CanAvoidLoss player position)
    (hbound : position.toMove = player → ∀ x, SafePick position x → lower < x) :
    check player position lower = true := by
  rw [check.eq_def]
  by_cases hn : position.IsTerminal
  · simpa [hn] using (can_avoid_loss_iff_terminal_outcome_ne_loss player position hn).mp hsafe
  · by_cases hm : position.toMove = player
    · rw [ite_eq_right hn, ite_eq_left hm]
      rw [Finset.fold_op_rel_iff_or (r := fun _ value : Bool ↦ value = true) (c := true)
        (by simp)]
      simp only [Bool.false_eq_true, false_or, Finset.mem_attach, Bool.and_eq_true,
        decide_eq_true_eq]
      have hcurrent : CanAvoidLoss position.toMove position := by simpa [hm] using hsafe
      obtain ⟨x, hleast⟩ := exists_least_safe position hn hcurrent
      refine ⟨⟨x, hleast.1.1⟩, True.intro, hbound hm x hleast.1, ?_⟩
      apply check_complete player (position.afterPick x) x
      · intro y hy
        exact hpositive y (Finset.mem_of_mem_erase hy)
      · simpa [hm] using hleast.1.2
      · intro hchildOwner y hy
        by_cases hd : x < position.deficit
        · exact safe_next_gt position x y hn hleast hd hy
        · simp [GamePosition.afterPick, hd, hm] at hchildOwner
    · rw [ite_eq_right hn, ite_eq_right hm]
      rw [Finset.fold_op_rel_iff_and (r := fun _ value : Bool ↦ value = true) (c := true)
        (by simp)]
      simp only [true_and, Finset.mem_attach]
      intro x _
      apply check_complete player (position.afterPick x.1) 0
      · intro y hy
        exact hpositive y (Finset.mem_of_mem_erase hy)
      · exact (can_avoid_loss_iff_forall_safe_moves player position hn hm).mp hsafe x.1 x.2
      · intro _ y hy
        exact hpositive y (Finset.mem_of_mem_erase hy.1)
termination_by position.remaining.card
decreasing_by
  all_goals
    apply GamePosition.remaining_card_after_pick_lt
    first | assumption | exact hleast.1.1 | exact x.2

/-- For positive counters, increasing protected turns preserve exactly the original nonloss. -/
theorem check_iff (player : Player) (position : GamePosition)
    (hpositive : ∀ x ∈ position.remaining, 0 < x) :
    check player position 0 = true ↔ CanAvoidLoss player position := by
  exact ⟨check_sound player position 0, fun h ↦
    check_complete player position 0 hpositive h (fun _ x hx ↦ hpositive x hx.1)⟩

/-- The first-pair interval is the existing pair-deletion endpoint. -/
theorem first_pair_eq (N : ℕ) :
    (⟨Finset.Icc 3 N, 1⟩ : Position) = pairDeletionPosition N 1 2 := by
  rw [pairDeletionPosition, Position.mk.injEq]
  constructor
  · ext x
    simp
    omega
  · rfl

/-- Each protected player may use increasing turns at the first-pair endpoint,
against every legal opponent reply. -/
theorem first_pair_check_iff (N : ℕ) (player : Player) :
    check player ⟨⟨Finset.Icc 3 N, 1⟩, .p1⟩ 0 = true ↔
      CanAvoidLoss player ⟨pairDeletionPosition N 1 2, .p1⟩ := by
  rw [← first_pair_eq]
  apply check_iff
  intro x hx
  have := (Finset.mem_Icc.mp hx).1
  omega

/-- The first-pair game is reached by the actual opening one followed by counter two. -/
theorem first_pair_reachable (N : ℕ) (hN : 2 ≤ N) :
    ReachableFromOpening N 1 ⟨⟨Finset.Icc 3 N, 1⟩, .p1⟩ := by
  let p := GamePosition.afterOpening (Finset.Icc 1 N) 1
  have hx : p.LegalMove 2 := by
    simp [p, GamePosition.LegalMove, GamePosition.afterOpening, afterOpening]
    omega
  have hsum : 2 ≤ p.remaining.sum id :=
    Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx
  have hn : ¬ p.IsTerminal := by
    apply (GamePosition.not_is_terminal_iff p).mpr
    exact ⟨Finset.nonempty_iff_ne_empty.mp ⟨2, hx⟩, by change ¬ p.remaining.sum id < 1; omega⟩
  have hr : ReachableFromOpening N 1 p :=
    reachable_from_opening_root N 1 (by simp; omega)
  have hnext := hr.after_pick 2 hn hx
  rw [first_pair_eq]
  simpa [p, GamePosition.afterOpening, afterOpening, GamePosition.afterPick,
    Position.afterPick, pairDeletionPosition, Player.other] using hnext

/-- Both restricted nonloss checks characterize the first-pair draw exactly. -/
theorem first_pair_draw_iff (N : ℕ) :
    (⟨Finset.Icc 3 N, 1⟩ : Position).value = .draw ↔
      check .p1 ⟨⟨Finset.Icc 3 N, 1⟩, .p1⟩ 0 = true ∧
      check .p2 ⟨⟨Finset.Icc 3 N, 1⟩, .p1⟩ 0 = true := by
  rw [first_pair_check_iff, first_pair_check_iff, first_pair_eq]
  simp [can_avoid_loss_iff_value]

/-- The recovered interval reduction may use the increasing-turn first-pair certificate. -/
theorem interval_draw_of_checks (N : ℕ) (hN : 2 ≤ N)
    (hpairs : LowerPairDeletionNonloss N)
    (hp1 : check .p1 ⟨⟨Finset.Icc 3 N, 1⟩, .p1⟩ 0 = true)
    (hp2 : check .p2 ⟨⟨Finset.Icc 3 N, 1⟩, .p1⟩ 0 = true) :
    value (Finset.Icc 1 N) = .draw := by
  apply value_Icc_eq_draw_of_lower_pair_deletion_nonloss N hN hpairs
  rw [← first_pair_eq]
  exact (first_pair_draw_iff N).mpr ⟨hp1, hp2⟩

/-- One complete turn of the canonical least-safe policy. This is not an outcome invariant. -/
inductive LeastSafeTurn : GamePosition → List ℕ → GamePosition → Prop
  | finish (position : GamePosition) (x : ℕ)
      (least : LeastSafePick position x) (catches : position.deficit ≤ x) :
      LeastSafeTurn position [x] (position.afterPick x)
  | more (position : GamePosition) (x : ℕ) (xs : List ℕ) (after : GamePosition)
      (least : LeastSafePick position x) (behind : x < position.deficit)
      (tail : LeastSafeTurn (position.afterPick x) xs after) :
      LeastSafeTurn position (x :: xs) after

/-- The canonical policy produces actual legal completed turns. -/
theorem LeastSafeTurn.completed {before after : GamePosition} {xs : List ℕ}
    (trace : LeastSafeTurn before xs after) : CompletedTurn before xs after := by
  induction trace with
  | finish p x hx hd => exact CompletedTurn.finish p x hx.1.1 hd
  | more p x xs after hx hd _ ih => exact CompletedTurn.more p x xs after hx.1.1 hd ih

/-- The first pick of a canonical turn is least safe. -/
theorem LeastSafeTurn.head_least {before after : GamePosition} {x : ℕ} {xs : List ℕ}
    (trace : LeastSafeTurn before (x :: xs) after) : LeastSafePick before x := by
  cases trace <;> assumption

/-- Every nonlosing nonterminal friendly state admits a complete canonical safe turn. -/
theorem exists_least_safe_turn (position : GamePosition) (hn : ¬ position.IsTerminal)
    (hsafe : CanAvoidLoss position.toMove position) :
    ∃ xs after, LeastSafeTurn position xs after ∧ CanAvoidLoss position.toMove after := by
  obtain ⟨x, hleast⟩ := exists_least_safe position hn hsafe
  by_cases hd : x < position.deficit
  · have hchild := hleast.1.2
    rw [← position.to_move_after_pick_of_lt x hd] at hchild
    obtain ⟨xs, after, hturn, hsafeAfter⟩ := exists_least_safe_turn (position.afterPick x)
      (nonterminal_after_continue position x hn hleast.1.1 hd) hchild
    exact ⟨x :: xs, after, LeastSafeTurn.more position x xs after hleast hd hturn,
      by simpa only [position.to_move_after_pick_of_lt x hd] using hsafeAfter⟩
  · exact ⟨[x], position.afterPick x, LeastSafeTurn.finish position x hleast (by omega),
      hleast.1.2⟩
termination_by position.remaining.card
decreasing_by
  exact position.remaining_card_after_pick_lt x hleast.1.1

/-- Every complete canonical turn is strictly increasing, including its final catching pick. -/
theorem LeastSafeTurn.pairwise {before after : GamePosition} {xs : List ℕ}
    (trace : LeastSafeTurn before xs after) : xs.Pairwise (· < ·) := by
  induction trace with
  | finish => simp
  | more p x xs after hx hd tail ih =>
    cases xs with
    | nil => exact False.elim (tail.completed.picks_nonempty rfl)
    | cons y ys =>
      have hn :=
        (CompletedTurn.more p x (y :: ys) after hx.1.1 hd tail.completed).before_not_terminal
      have hxy := safe_next_gt p x y hn hx hd tail.head_least.1
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact hxy.trans ((List.pairwise_cons.mp ih).1 z hz)

/-- An increasing positive list has at least the mass of the corresponding initial segment. -/
theorem increasing_sum_bound (xs : List ℕ) (lower : ℕ)
    (hincreasing : xs.Pairwise (· < ·)) (hpositive : ∀ x ∈ xs, lower + 1 ≤ x) :
    xs.length * (xs.length + 1) + 2 * lower * xs.length ≤ 2 * xs.sum := by
  induction xs generalizing lower with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hincreasing
    have hx : lower + 1 ≤ x := hpositive x (by simp)
    have hrest := ih x htail (fun y hy ↦ Nat.succ_le_of_lt (hhead y hy))
    have hmul := Nat.mul_le_mul_left (xs.length + 1) hx
    simp only [List.length_cons, List.sum_cons]
    nlinarith

/-- A canonical turn with `k` preparation picks obeys `k*(k+1) < 2*N`. -/
theorem LeastSafeTurn.preparation_length_bound
    {before after : GamePosition} {preparation : List ℕ} {final N : ℕ}
    (trace : LeastSafeTurn before (preparation ++ [final]) after)
    (hpositive : ∀ x ∈ before.remaining, 0 < x)
    (hdeficit : before.deficit ≤ N) (hN : 0 < N) :
    preparation.length * (preparation.length + 1) < 2 * N := by
  have hinc : preparation.Pairwise (· < ·) := (List.pairwise_append.mp trace.pairwise).1
  have hmass := increasing_sum_bound preparation 0 hinc (by
    intro x hx
    have hmem : x ∈ (preparation ++ [final]).toFinset := by simp [hx]
    exact hpositive x (trace.completed.picks_subset_remaining hmem))
  rcases trace.completed.preparation_sum_lt_or_empty with hempty | hsum
  · simp [hempty]
    omega
  · nlinarith

/-- The same square-root preparation bound holds anywhere reachable in an interval game. -/
theorem LeastSafeTurn.reachable_preparation_length_bound
    {N opening : ℕ} {before after : GamePosition} {preparation : List ℕ} {final : ℕ}
    (trace : LeastSafeTurn before (preparation ++ [final]) after)
    (hreachable : ReachableFromOpening N opening before) (hN : 0 < N) :
    preparation.length * (preparation.length + 1) < 2 * N := by
  apply trace.preparation_length_bound _ hreachable.deficit_le hN
  intro x hx
  exact (Finset.mem_Icc.mp (hreachable.remaining_subset_Icc hx)).1

end CatchUp.Increasing
