/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/TwoBufferProtocol.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.ScoreDebtRepairCertificates

/-!
# Finite causal two-buffer protocols

The controller commits to a side before an adversarial move is revealed. Every
actual opponent move and every strictly winning shadow protected reply is covered.
The shadow's winning-reply predicate constrains the supplied strategy, not the debt
invariant. The inductive protocol enforces atomic buffer bounds and terminal margins.
A successful executable policy check constructs a protocol without trusting search.

Buffers count the raw `remaining` fields, including stranded counters at early
terminal states. Completion accounts for their payoff without an erase transition.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp.TwoBuffer
local instance (u v : GamePosition) : Decidable (ScoreDebtRepair.TwoBuffer u v) := by
  unfold ScoreDebtRepair.TwoBuffer
  infer_instance
/-- The four causal scheduling actions. -/
inductive Action where
  | actualPick (x : ℕ)
  | actualOpponent
  | shadowPick (x : ℕ)
  | shadowStrategy
  deriving DecidableEq
/-- Executable strict-win preservation for a supplied shadow strategy. -/
def shadowGood (v : GamePosition) (x : ℕ) : Bool :=
  !(CatchUpSearch.CanAvoidLossClassifier.check .p2 (v.afterPick x))

/-- A finite causal protocol. Universal branches reveal moves only after side selection. -/
inductive Protocol : GamePosition → GamePosition → Prop
  | finish {u v} (buffer : ScoreDebtRepair.TwoBuffer u v)
      (hu : u.IsTerminal) (hv : v.IsTerminal)
      (margin : v.completedMargin .p1 - 2 ≤ u.completedMargin .p1) : Protocol u v
  | actualPick {u v} (buffer : ScoreDebtRepair.TwoBuffer u v)
      (ht : ¬u.IsTerminal) (turn : u.toMove = .p1) (x : ℕ) (legal : x ∈ u.remaining)
      (next : Protocol (u.afterPick x) v) : Protocol u v
  | actualOpponent {u v} (buffer : ScoreDebtRepair.TwoBuffer u v)
      (ht : ¬u.IsTerminal) (turn : u.toMove = .p2)
      (next : ∀ x ∈ u.remaining, Protocol (u.afterPick x) v) : Protocol u v
  | shadowPick {u v} (buffer : ScoreDebtRepair.TwoBuffer u v)
      (ht : ¬v.IsTerminal) (turn : v.toMove = .p2) (x : ℕ) (legal : x ∈ v.remaining)
      (next : Protocol u (v.afterPick x)) : Protocol u v
  | shadowStrategy {u v} (buffer : ScoreDebtRepair.TwoBuffer u v)
      (ht : ¬v.IsTerminal) (turn : v.toMove = .p1)
      (nonempty : ∃ x ∈ v.remaining, ¬CanAvoidLoss .p2 (v.afterPick x))
      (next : ∀ x ∈ v.remaining, ¬CanAvoidLoss .p2 (v.afterPick x) →
        Protocol u (v.afterPick x)) : Protocol u v

/-- Check a finite policy with a pick budget; each recursive step consumes one counter. -/
def runCheck (policy : GamePosition → GamePosition → Action) :
    ℕ → GamePosition → GamePosition → Bool
  | 0, u, v => decide (ScoreDebtRepair.TwoBuffer u v) &&
      decide (u.IsTerminal ∧ v.IsTerminal) &&
      decide (v.completedMargin .p1 - 2 ≤ u.completedMargin .p1)
  | n+1, u, v =>
    decide (ScoreDebtRepair.TwoBuffer u v) &&
    if u.IsTerminal ∧ v.IsTerminal then
      decide (v.completedMargin .p1 - 2 ≤ u.completedMargin .p1)
    else match policy u v with
    | .actualPick x => decide (¬u.IsTerminal ∧ u.toMove = .p1 ∧ x ∈ u.remaining) &&
        runCheck policy n (u.afterPick x) v
    | .actualOpponent => decide (¬u.IsTerminal ∧ u.toMove = .p2) &&
        decide (∀ x ∈ u.remaining, runCheck policy n (u.afterPick x) v = true)
    | .shadowPick x => decide (¬v.IsTerminal ∧ v.toMove = .p2 ∧ x ∈ v.remaining) &&
        runCheck policy n u (v.afterPick x)
    | .shadowStrategy => decide (¬v.IsTerminal ∧ v.toMove = .p1) &&
        decide (∃ x ∈ v.remaining, shadowGood v x = true) &&
        decide (∀ x ∈ v.remaining, shadowGood v x = true →
          runCheck policy n u (v.afterPick x) = true)

/-- The shadow-reply filter is precisely the opponent's inability to avoid loss. -/
theorem shadow_good_iff (v : GamePosition) (x : ℕ) :
    shadowGood v x = true ↔ ¬CanAvoidLoss .p2 (v.afterPick x) := by
  simp only [shadowGood, Bool.not_eq_true', Bool.eq_false_iff]
  exact not_congr (CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff _ _)

/-- A successful finite check proves the full inductive causal protocol. -/
theorem run_check_sound (policy : GamePosition → GamePosition → Action)
    (n : ℕ) (u v : GamePosition) (h : runCheck policy n u v = true) :
    Protocol u v := by
  induction n generalizing u v with
  | zero =>
    simp only [runCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Protocol.finish h.1.1 h.1.2.1 h.1.2.2 h.2
  | succ n ih =>
    simp only [runCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hb, h⟩ := h
    split_ifs at h with ht
    · exact Protocol.finish hb ht.1 ht.2 (of_decide_eq_true h)
    · cases ha : policy u v <;> simp only [ha, Bool.and_eq_true, decide_eq_true_eq] at h
      · exact Protocol.actualPick hb h.1.1 h.1.2.1 _ h.1.2.2 (ih _ _ h.2)
      · exact Protocol.actualOpponent hb h.1.1 h.1.2 (fun x hx ↦ ih _ _ (h.2 x hx))
      · exact Protocol.shadowPick hb h.1.1 h.1.2.1 _ h.1.2.2 (ih _ _ h.2)
      · exact Protocol.shadowStrategy hb h.1.1.1 h.1.1.2
          (by simpa only [shadow_good_iff] using h.1.2)
          (fun x hx hw ↦ ih _ _ (h.2 x hx ((shadow_good_iff v x).mpr hw)))
end CatchUp.TwoBuffer
