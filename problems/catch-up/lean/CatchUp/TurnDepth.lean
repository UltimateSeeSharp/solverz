/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/TurnDepth.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.CompletedTurn

/-!
# A lower bound on whole-turn closure depth

The final counter of a completed turn bounds that turn's increase in the leading score.
Tracking these increases gives a barrier on reaching a terminal or score-sum draw leaf.
This does not supply a strategy or settle the interval conjecture.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.TurnDepth

/-- A completed turn's overshoot is at most its actual final counter, including tied starts. -/
theorem overshoot_le_final {before : GamePosition} {chosen : Finset ℕ} {final : ℕ}
    (turn : TurnSet before chosen final) :
    (completedTurnEndpoint before chosen).deficit ≤ final := by
  rcases turn.preparation_below with he | hl
  · simp [completedTurnEndpoint, he]
  · have hs := Finset.sum_erase_add chosen (fun x : ℕ ↦ x) turn.final_mem
    change (chosen.sum (fun x ↦ x)) - before.deficit ≤ final
    omega

/-- A completed turn conserves remaining mass after splitting off its two deficits. -/
theorem turn_mass {before : GamePosition} {chosen : Finset ℕ} {final : ℕ}
    (turn : TurnSet before chosen final) :
    before.remaining.sum (fun x ↦ x) = before.deficit +
      (completedTurnEndpoint before chosen).deficit +
        (completedTurnEndpoint before chosen).remaining.sum (fun x ↦ x) := by
  have hs := Finset.sum_sdiff (f := fun x : ℕ ↦ x) turn.chosen_subset
  have hc := turn.catches
  simp only [completedTurnEndpoint]
  omega

/-- Consecutive arbitrary legal whole turns, recording final counters and total overshoot. -/
inductive TurnChain : GamePosition → List ℕ → ℕ → GamePosition → Prop
  | nil (before : GamePosition) : TurnChain before [] 0 before
  | cons {before after : GamePosition} {chosen : Finset ℕ} {final : ℕ}
      {finals : List ℕ} {rise : ℕ}
      (turn : TurnSet before chosen final)
      (tail : TurnChain (completedTurnEndpoint before chosen) finals rise after) :
      TurnChain before (final :: finals)
        ((completedTurnEndpoint before chosen).deficit + rise) after

/-- The exact conservation identity along any sequence of completed turns. -/
theorem TurnChain.conservation {before after : GamePosition} {finals : List ℕ} {rise : ℕ}
    (chain : TurnChain before finals rise after) :
    before.remaining.sum (fun x ↦ x) + after.deficit =
      before.deficit + 2 * rise + after.remaining.sum (fun x ↦ x) := by
  induction chain with
  | nil => omega
  | cons turn tail ih =>
    have ht := turn_mass turn
    omega

/-- The total increase of the leading score is bounded by the sum of turn-final counters. -/
theorem TurnChain.rise_le_finals_sum
    {before after : GamePosition} {finals : List ℕ} {rise : ℕ}
    (chain : TurnChain before finals rise after) : rise ≤ finals.sum := by
  induction chain with
  | nil => simp
  | cons turn tail ih =>
    have ht := overshoot_le_final turn
    simp only [List.sum_cons]
    omega

/-- Every recorded final counter was available at the beginning of the chain. -/
theorem TurnChain.finals_subset_remaining
    {before after : GamePosition} {finals : List ℕ} {rise : ℕ}
    (chain : TurnChain before finals rise after) : finals.toFinset ⊆ before.remaining := by
  induction chain with
  | nil => simp
  | cons turn tail ih =>
    intro x hx
    simp only [List.toFinset_cons, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact turn.chosen_subset turn.final_mem
    · exact (Finset.mem_sdiff.mp (ih hx)).1

/-- Recorded final counters do not repeat across different completed turns. -/
theorem TurnChain.finals_nodup
    {before after : GamePosition} {finals : List ℕ} {rise : ℕ}
    (chain : TurnChain before finals rise after) : finals.Nodup := by
  induction chain with
  | nil => simp
  | cons turn tail ih =>
    rw [List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hf
    have hm := tail.finals_subset_remaining (List.mem_toFinset.mpr hf)
    exact (Finset.mem_sdiff.mp hm).2 turn.final_mem

/-- A uniform upper bound on counters bounds the final-counter sum. -/
theorem TurnChain.finals_sum_le
    {before after : GamePosition} {finals : List ℕ} {rise M : ℕ}
    (chain : TurnChain before finals rise after)
    (hM : ∀ x ∈ before.remaining, x ≤ M) : finals.sum ≤ finals.length * M := by
  induction chain with
  | nil => simp
  | cons turn tail ih =>
    have hf := hM _ (turn.chosen_subset turn.final_mem)
    have ht := ih (fun x hx ↦ hM x (Finset.mem_sdiff.mp hx).1)
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- Exact conservation after the forced single opening pick. -/
theorem TurnChain.opening_conservation
    {S : Finset ℕ} {x rise : ℕ} {finals : List ℕ} {after : GamePosition}
    (hx : x ∈ S) (chain : TurnChain (GamePosition.afterOpening S x) finals rise after) :
    S.sum (fun y ↦ y) + after.deficit =
      2 * (x + rise) + after.remaining.sum (fun y ↦ y) := by
  have hc := chain.conservation
  have hs := Finset.sum_erase_add S (fun y : ℕ ↦ y) hx
  simp only [GamePosition.afterOpening, afterOpening] at hc
  omega

/-- Reaching a terminal or score-sum leaf requires sufficient total final-counter mass. -/
theorem TurnChain.closure_barrier
    {S : Finset ℕ} {x rise : ℕ} {finals : List ℕ} {after : GamePosition}
    (hx : x ∈ S) (chain : TurnChain (GamePosition.afterOpening S x) finals rise after)
    (hleaf : after.remaining.sum (fun y ↦ y) ≤ after.deficit) :
    S.sum (fun y ↦ y) ≤ 2 * (x + finals.sum) := by
  have hc := chain.opening_conservation hx
  have hr := chain.rise_le_finals_sum
  omega

/-- Every ordered legal completed turn is admitted, with its actual final counter. -/
theorem TurnChain.cons_completed
    {before middle after : GamePosition} {preparation finals : List ℕ} {final rise : ℕ}
    (trace : CompletedTurn before (preparation ++ [final]) middle)
    (tail : TurnChain middle finals rise after) :
    TurnChain before (final :: finals) (middle.deficit + rise) after := by
  have he := trace.after_eq_endpoint
  rw [he] at tail ⊢
  apply TurnChain.cons _ tail
  simpa using trace.turn_set

/-- Twice the total of an original interval. -/
theorem interval_sum_twice (N : ℕ) :
    2 * (Finset.Icc 1 N).sum (fun y ↦ y) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    nlinarith

/-- A terminal or score-sum leaf from an interval needs a number of turns growing with N. -/
theorem interval_closure_depth
    {N x rise : ℕ} {finals : List ℕ} {after : GamePosition}
    (hx : x ∈ Finset.Icc 1 N)
    (chain : TurnChain (GamePosition.afterOpening (Finset.Icc 1 N) x) finals rise after)
    (hleaf : after.remaining.sum (fun y ↦ y) ≤ after.deficit) :
    N + 1 ≤ 4 * (finals.length + 1) := by
  have hb := chain.closure_barrier hx hleaf
  have hf := chain.finals_sum_le (M := N) (by
    intro y hy
    exact (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hy)).2)
  have htotal := interval_sum_twice N
  have hxN := Finset.mem_Icc.mp hx
  nlinarith

/-- The opening counter and all recorded final counters are distinct. -/
theorem TurnChain.opening_finals_nodup
    {S : Finset ℕ} {x rise : ℕ} {finals : List ℕ} {after : GamePosition}
    (chain : TurnChain (GamePosition.afterOpening S x) finals rise after) :
    (x :: finals).Nodup := by
  rw [List.nodup_cons]
  refine ⟨?_, chain.finals_nodup⟩
  intro hx
  have hm := chain.finals_subset_remaining (List.mem_toFinset.mpr hx)
  change x ∈ S.erase x at hm
  exact (Finset.mem_erase.mp hm).1 rfl

/-- The opening and all final counters belong to the original support. -/
theorem TurnChain.opening_finals_subset
    {S : Finset ℕ} {x rise : ℕ} {finals : List ℕ} {after : GamePosition}
    (hx : x ∈ S) (chain : TurnChain (GamePosition.afterOpening S x) finals rise after) :
    (x :: finals).toFinset ⊆ S := by
  intro y hy
  simp only [List.toFinset_cons, Finset.mem_insert] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact Finset.mem_of_mem_erase (chain.finals_subset_remaining hy)

/-- A subtraction-free sharp bound for the sum of distinct interval counters. -/
theorem interval_subset_sum_core (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N) :
    2 * S.sum (fun x ↦ x) + S.card * S.card ≤ S.card * (2 * N + 1) := by
  induction N generalizing S with
  | zero =>
    have he : S = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := hS hx
      simp only [Finset.mem_Icc] at h
      omega
    simp [he]
  | succ N ih =>
    by_cases hmem : N + 1 ∈ S
    · have hsub : S.erase (N + 1) ⊆ Finset.Icc 1 N := by
        intro x hx
        have h := hS (Finset.mem_of_mem_erase hx)
        have hn := Finset.ne_of_mem_erase hx
        simp only [Finset.mem_Icc] at h ⊢
        omega
      have hi := ih (S.erase (N + 1)) hsub
      have hs := Finset.sum_erase_add S (fun x ↦ x) hmem
      have hc := Finset.card_erase_add_one hmem
      rw [← hc, ← hs]
      nlinarith
    · have hsub : S ⊆ Finset.Icc 1 N := by
        intro x hx
        have h := hS hx
        have hn : x ≠ N + 1 := by intro he; subst x; exact hmem hx
        simp only [Finset.mem_Icc] at h ⊢
        omega
      have hi := ih S hsub
      nlinarith

/-- The largest possible sum of m distinct interval counters is the sum of the largest m. -/
theorem interval_subset_sum_bound (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N) :
    2 * S.sum (fun x ↦ x) ≤ S.card * (2 * N - S.card + 1) := by
  have hc : S.card ≤ N := by
    calc
      S.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hS
      _ = N := by simp
  have hi := interval_subset_sum_core N S hS
  have he : S.card * (2 * N - S.card + 1) + S.card * S.card =
      S.card * (2 * N + 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  omega

/-- Distinctness sharpens the linear bound on closure depth. -/
theorem interval_closure_depth_sharp
    {N x rise : ℕ} {finals : List ℕ} {after : GamePosition}
    (hx : x ∈ Finset.Icc 1 N)
    (chain : TurnChain (GamePosition.afterOpening (Finset.Icc 1 N) x) finals rise after)
    (hleaf : after.remaining.sum (fun y ↦ y) ≤ after.deficit) :
    N * (N + 1) / 2 ≤ (finals.length + 1) * (2 * N - finals.length) := by
  have hb := chain.closure_barrier hx hleaf
  have hp := interval_subset_sum_bound N (x :: finals).toFinset
    (chain.opening_finals_subset hx)
  have hn := chain.opening_finals_nodup
  have hc : (x :: finals).toFinset.card = finals.length + 1 := by
    simpa using List.toFinset_card_of_nodup hn
  have hs : (x :: finals).toFinset.sum (fun y ↦ y) = x + finals.sum := by
    simpa using List.sum_toFinset (fun y : ℕ ↦ y) hn
  have hcard := Finset.card_le_card (chain.opening_finals_subset hx)
  have htotal := interval_sum_twice N
  rw [hc, hs] at hp
  rw [hc] at hcard
  have hlen : finals.length + 1 ≤ N := by simpa using hcard
  have hsub : 2 * N - (finals.length + 1) + 1 = 2 * N - finals.length := by omega
  rw [hsub] at hp
  omega

/-- Every terminal endpoint is among the leaves controlled by the closure barrier. -/
theorem terminal_sum_le_deficit {after : GamePosition} (hterminal : after.IsTerminal) :
    after.remaining.sum (fun y ↦ y) ≤ after.deficit := by
  rcases hterminal with hempty | hsmall
  · simp [hempty]
  · exact Nat.le_of_lt hsmall

/-- In particular, every terminal whole-turn line obeys the interval depth bound. -/
theorem interval_terminal_depth
    {N x rise : ℕ} {finals : List ℕ} {after : GamePosition}
    (hx : x ∈ Finset.Icc 1 N)
    (chain : TurnChain (GamePosition.afterOpening (Finset.Icc 1 N) x) finals rise after)
    (hterminal : after.IsTerminal) : N + 1 ≤ 4 * (finals.length + 1) :=
  interval_closure_depth hx chain (terminal_sum_le_deficit hterminal)

end CatchUp.TurnDepth
