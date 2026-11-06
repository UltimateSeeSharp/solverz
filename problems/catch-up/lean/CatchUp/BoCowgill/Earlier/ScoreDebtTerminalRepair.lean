/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/ScoreDebtTerminalRepair.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.Earlier.CompletedMargin

/-!
# A causal terminal repayment gadget

For every natural parameter `k`, protect player one in the actual position
`({k + 4, 2 * k + 5, 2 * k + 6}, k + 5, p2)`. Taking the largest available counter
on protected turns guarantees completed margin zero or two against every
opponent move. In the shadow position `({k + 4, 2 * k + 6}, k + 4, p2)`, choose
`2 * k + 6` for the opponent; the protected reply `k + 4` is forced and gives
margin two. The invariant is a finite list of explicit arithmetic states,
not an outcome predicate. This is a terminal repair gadget, not a global
adjacent-hole translator.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.ScoreDebtRepair

/-- Actual root of the terminal repayment family. -/
def actualRoot (k : ℕ) : GamePosition :=
  ⟨⟨{k + 4, 2 * k + 5, 2 * k + 6}, k + 5⟩, .p2⟩
/-- Shadow root, with the middle counter absent and the deficit one smaller. -/
def shadowRoot (k : ℕ) : GamePosition :=
  ⟨⟨{k + 4, 2 * k + 6}, k + 4⟩, .p2⟩
/-- Structural phases of the max-pick controller; terminal phases retain the true mover. -/
inductive Phase (k : ℕ) : GamePosition → Prop
  | root : Phase k (actualRoot k)
  | low : Phase k ⟨⟨{2 * k + 5, 2 * k + 6}, 1⟩, .p2⟩
  | middle : Phase k ⟨⟨{k + 4, 2 * k + 6}, k⟩, .p1⟩
  | high : Phase k ⟨⟨{k + 4, 2 * k + 5}, k + 1⟩, .p1⟩
  | lowMiddle : Phase k ⟨⟨{2 * k + 6}, 2 * k + 4⟩, .p1⟩
  | lowHigh : Phase k ⟨⟨{2 * k + 5}, 2 * k + 5⟩, .p1⟩
  | highMiddle : Phase k ⟨⟨{k + 4}, k + 4⟩, .p2⟩
  | middleHigh : Phase k ⟨⟨{k + 4}, k + 6⟩, .p2⟩
  | win : Phase k ⟨⟨∅, 2⟩, .p2⟩
  | draw (player : Player) : Phase k ⟨⟨∅, 0⟩, player⟩
/-- On protected turns pick a largest counter; leave adversary turns unrestricted. -/
def Greedy (p : GamePosition) (x : ℕ) : Prop :=
  p.toMove = .p1 → ∀ z ∈ p.remaining, z ≤ x
/-- Every adversary pick and every legal protected max pick preserves the phase invariant. -/
theorem phase_closed {k : ℕ} {p : GamePosition} (hp : Phase k p)
    (x : ℕ) (hx : p.LegalMove x) (ht : ¬p.IsTerminal) (hg : Greedy p x) :
    Phase k (p.afterPick x) := by
  cases hp
  case root =>
    simp only [actualRoot, GamePosition.LegalMove, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · convert Phase.low (k := k) using 1
      · simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) [actualRoot, GamePosition.afterPick, Position.afterPick]
    · convert Phase.middle (k := k) using 1
      · simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) [actualRoot, GamePosition.afterPick, Position.afterPick,
          Player.other, Finset.erase_insert_of_ne, Finset.erase_eq_of_notMem] ; split_ifs <;> omega
    · convert Phase.high (k := k) using 1
      · simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) [actualRoot, GamePosition.afterPick, Position.afterPick,
          Player.other, Finset.erase_insert_of_ne] ; refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | omega | (exfalso; omega) | exact ite_eq_right ‹_›
  case low =>
    simp only [GamePosition.LegalMove, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · convert Phase.lowMiddle (k := k) using 1
      · simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) [GamePosition.afterPick, Position.afterPick,
          Player.other, Finset.erase_eq_of_notMem]
    · convert Phase.lowHigh (k := k) using 1
      · simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) [GamePosition.afterPick, Position.afterPick,
          Player.other, Finset.erase_insert_of_ne]
  case middle =>
    have hmax := hg rfl (2 * k + 6) (by simp)
    simp only [GamePosition.LegalMove, Finset.mem_insert, Finset.mem_singleton] at hx
    have he : x = 2 * k + 6 := by omega
    subst x
    convert Phase.middleHigh (k := k) using 1
    · simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) [GamePosition.afterPick, Position.afterPick,
        Player.other, Finset.erase_insert_of_ne] ;
      split_ifs <;> omega
  case high =>
    have hmax := hg rfl (2 * k + 5) (by simp)
    simp only [GamePosition.LegalMove, Finset.mem_insert, Finset.mem_singleton] at hx
    have he : x = 2 * k + 5 := by omega
    subst x
    convert Phase.highMiddle (k := k) using 1
    · simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) [GamePosition.afterPick, Position.afterPick,
        Player.other, Finset.erase_insert_of_ne] ;
      split_ifs <;> omega
  case lowMiddle =>
    have he : x = 2 * k + 6 := by simpa [GamePosition.LegalMove] using hx
    subst x
    convert Phase.win (k := k) using 1
    · simp [GamePosition.afterPick, Position.afterPick, Player.other]
  case lowHigh =>
    have he : x = 2 * k + 5 := by simpa [GamePosition.LegalMove] using hx
    subst x
    simpa [GamePosition.afterPick, Position.afterPick, Player.other] using
      Phase.draw (k := k) .p2
  case highMiddle =>
    have he : x = k + 4 := by simpa [GamePosition.LegalMove] using hx
    subst x
    simpa [GamePosition.afterPick, Position.afterPick, Player.other] using
      Phase.draw (k := k) .p1
  case middleHigh =>
    simp [GamePosition.IsTerminal] at ht
  case win => simp [GamePosition.LegalMove] at hx
  case draw => simp [GamePosition.LegalMove] at hx

/-- Terminal phases complete to margin zero or two, including the early-loss cutoff. -/
theorem phase_terminal_margin {k : ℕ} {p : GamePosition}
    (hp : Phase k p) (ht : p.IsTerminal) :
    p.completedMargin .p1 = 0 ∨ p.completedMargin .p1 = 2 := by
  cases hp
  case draw player =>
    cases player <;> simp [GamePosition.completedMargin, GamePosition.p1ScoreBalance,
      Player.scoreCoefficient]
  all_goals
    simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
      [actualRoot, GamePosition.IsTerminal, Finset.sum_insert,
        GamePosition.completedMargin, GamePosition.p1ScoreBalance,
        Player.scoreCoefficient, -Nat.cast_sum] at * <;> omega

/-- A causal local policy predicate on a pick list, separate from its legal step trace. -/
def GreedyPicks : GamePosition → List ℕ → Prop
  | _, [] => True
  | p, x :: xs => p.LegalMove x ∧ Greedy p x ∧ GreedyPicks (p.afterPick x) xs

/-- The structural phase invariant persists along every legal controlled trace. -/
theorem phase_after_trace {k : ℕ} {p q : GamePosition} {xs : List ℕ}
    (trace : GamePosition.PickTrace p xs q) (hp : Phase k p) (hg : GreedyPicks p xs) :
    Phase k q := by
  induction trace with
  | nil => exact hp
  | cons p x xs q hs tail ih =>
      exact ih (phase_closed hp x hg.1 hs.1 hg.2.1) hg.2.2

/-- Every completed play of the explicit actual controller has margin zero or two. -/
theorem greedy_terminal_margin (k : ℕ) (q : GamePosition) (xs : List ℕ)
    (trace : GamePosition.PickTrace (actualRoot k) xs q)
    (hg : GreedyPicks (actualRoot k) xs) (ht : q.IsTerminal) :
    q.completedMargin .p1 = 0 ∨ q.completedMargin .p1 = 2 :=
  phase_terminal_margin (phase_after_trace trace (Phase.root) hg) ht

/-- The chosen shadow opponent pick leaves a singleton for the protected player. -/
theorem shadow_first (k : ℕ) :
    (shadowRoot k).afterPick (2 * k + 6) = ⟨⟨{k + 4}, k + 2⟩, .p1⟩ := by
  simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
    [shadowRoot, GamePosition.afterPick, Position.afterPick, Player.other,
      Finset.erase_insert_of_ne] ; refine ⟨?_, ?_⟩ <;> split_ifs <;> first | rfl | omega | (exfalso; omega) | exact ite_eq_right ‹_›

/-- The forced singleton reply completes the shadow game with margin two. -/
theorem shadow_second (k : ℕ) :
    (⟨⟨{k + 4}, k + 2⟩, .p1⟩ : GamePosition).afterPick (k + 4) =
      ⟨⟨∅, 2⟩, .p2⟩ := by
  simp [GamePosition.afterPick, Position.afterPick, Player.other]

/-- Both shadow picks are legal nonterminal game steps. -/
theorem shadow_trace (k : ℕ) :
    GamePosition.PickTrace (shadowRoot k) [2 * k + 6, k + 4] ⟨⟨∅, 2⟩, .p2⟩ := by
  apply GamePosition.PickTrace.cons
  · apply GamePosition.step_after_pick
    · simp (disch := first | omega |
          (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) [shadowRoot, GamePosition.IsTerminal, Finset.sum_insert]
    · simp [shadowRoot, GamePosition.LegalMove]
  · rw [shadow_first]
    apply GamePosition.PickTrace.cons
    · apply GamePosition.step_after_pick
      · simp [GamePosition.IsTerminal]
      · simp [GamePosition.LegalMove]
    · rw [shadow_second]
      exact GamePosition.PickTrace.nil _

/-- Every supplied strategy must make the same protected reply after our shadow pick. -/
theorem shadow_forced_reply (k x : ℕ)
    (hx : ((shadowRoot k).afterPick (2 * k + 6)).LegalMove x) : x = k + 4 := by
  rw [shadow_first] at hx
  simpa [GamePosition.LegalMove] using hx

/-- The actual max-pick policy and the explicit shadow trace satisfy the two-point certificate. -/
theorem repaired_margin_bound (k : ℕ) (q : GamePosition) (xs : List ℕ)
    (trace : GamePosition.PickTrace (actualRoot k) xs q)
    (hg : GreedyPicks (actualRoot k) xs) (ht : q.IsTerminal) :
    (⟨⟨∅, 2⟩, .p2⟩ : GamePosition).completedMargin .p1 - 2 ≤ q.completedMargin .p1 := by
  have hm := greedy_terminal_margin k q xs trace hg ht
  change 0 ≤ q.completedMargin .p1
  omega

/-- The policy always has a legal move before termination. -/
theorem greedy_legal_exists (p : GamePosition) (ht : ¬p.IsTerminal) :
    ∃ x, p.LegalMove x ∧ Greedy p x := by
  have hs : p.remaining.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr ((GamePosition.not_is_terminal_iff p).mp ht).1
  exact ⟨p.remaining.max' hs, Finset.max'_mem _ _, fun _ z hz ↦ Finset.le_max' _ z hz⟩

/-- Well-founded strategy semantics confirm nonloss from every structural phase. -/
theorem phase_can_avoid_loss (k : ℕ) (p : GamePosition) (hp : Phase k p) :
    CanAvoidLoss .p1 p := by
  induction p using
      (measure fun q : GamePosition ↦ q.remaining.card).wf.induction with
  | h p ih =>
      by_cases ht : p.IsTerminal
      · rw [can_avoid_loss_iff_terminal_outcome_ne_loss _ _ ht]
        have hm := phase_terminal_margin hp ht
        intro hl
        have hneg := (p.completion_sign .p1 ht).2.2.mp hl
        omega
      · by_cases hm : p.toMove = .p1
        · rw [can_avoid_loss_iff_exists_safe_move _ _ ht hm]
          obtain ⟨x, hx, hg⟩ := greedy_legal_exists p ht
          exact ⟨x, hx, ih (p.afterPick x) (p.remaining_card_after_pick_lt x hx)
            (phase_closed hp x hx ht hg)⟩
        · rw [can_avoid_loss_iff_forall_safe_moves _ _ ht hm]
          intro x hx
          exact ih (p.afterPick x) (p.remaining_card_after_pick_lt x hx)
            (phase_closed hp x hx ht (fun h ↦ False.elim (hm h)))

/-- The terminal repair family is nonlosing for the fixed protected player. -/
theorem actual_can_avoid_loss (k : ℕ) : CanAvoidLoss .p1 (actualRoot k) :=
  phase_can_avoid_loss k _ Phase.root

/-- At most two unmatched remaining counters on each side. -/
def TwoBuffer (u v : GamePosition) : Prop :=
  (u.remaining \ v.remaining).card ≤ 2 ∧ (v.remaining \ u.remaining).card ≤ 2

/-- Small residual supports imply the two-counter buffer condition. -/
theorem two_buffer_of_card_le (u v : GamePosition)
    (hu : u.remaining.card ≤ 2) (hv : v.remaining.card ≤ 2) : TwoBuffer u v := by
  exact ⟨(Finset.card_le_card Finset.sdiff_subset).trans hu,
    (Finset.card_le_card Finset.sdiff_subset).trans hv⟩

/-- Observing the first actual adversary pick leaves at most two counters. -/
theorem actual_after_pick_card (k x : ℕ) (hx : (actualRoot k).LegalMove x) :
    ((actualRoot k).afterPick x).remaining.card ≤ 2 := by
  have hc : (actualRoot k).remaining.card = 3 := by
    simp (disch := first | omega | (simp only [Finset.mem_insert, Finset.mem_singleton]; omega))
      [actualRoot]
  have hl := (actualRoot k).remaining_card_after_pick_lt x hx
  omega

/-- After observing one actual pick, every asynchronous legal continuation stays within buffer two. -/
theorem buffer_after_first_pick (k x : ℕ) (hx : (actualRoot k).LegalMove x)
    (u v : GamePosition) (us vs : List ℕ)
    (hu : GamePosition.PickTrace ((actualRoot k).afterPick x) us u)
    (hv : GamePosition.PickTrace (shadowRoot k) vs v) : TwoBuffer u v := by
  apply two_buffer_of_card_le
  · exact hu.remaining_card_le.trans (actual_after_pick_card k x hx)
  · have hc : (shadowRoot k).remaining.card = 2 := by
      simp (disch := first | omega | (simp only [Finset.mem_insert, Finset.mem_singleton]; omega)) [shadowRoot]
    have hl := hv.remaining_card_le
    omega

end CatchUp.ScoreDebtRepair
