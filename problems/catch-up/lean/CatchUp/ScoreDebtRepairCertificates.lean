/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ScoreDebtRepairCertificates.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.ScoreDebtTerminalRepair
public import CatchUp.AdjacentHoleExchangeObstruction

/-!
# Adjacent-hole parity and terminal-repair certificates

The initial effective totals are even under the requested hypotheses. Kernel-checked
legal traces connect the mandatory example to the parametric terminal repair and
certify two failed controller extensions. These are not a global translator.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUp
private theorem sum_Icc_one (N : ℕ) :
    (Finset.Icc 1 N).sum (fun x ↦ x) = N * (N + 1) / 2 := by
  have hs : Finset.Icc 1 N = (Finset.range (N + 1)).erase 0 := by
    ext x
    simp
    omega
  rw [hs]
  have hz : 0 ∈ Finset.range (N + 1) := by simp
  have he := Finset.sum_erase_add (Finset.range (N + 1)) (fun x ↦ x) hz
  simp only [add_zero] at he
  rw [he, Finset.sum_range_id]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]

/-- Removing an available consecutive pair from a tied punctured interval gives even effective total. -/
theorem punctured_neighbor_pair_even (N b c : ℕ) (hN : 11 ≤ N)
    (hb : 3 ≤ b) (hbN : b ≤ N) (he : Even (N * (N + 1) / 2))
    (hc : c ∈ Finset.Icc 1 N \ {1, b - 1, b})
    (hc1 : c + 1 ∈ Finset.Icc 1 N \ {1, b - 1, b}) :
    (1 + (((Finset.Icc 1 N \ {1, b - 1, b}).erase c).erase (c + 1)).sum
      (fun x ↦ x)) % 2 = 0 := by
  have hb1 : b - 1 + 1 = b := by omega
  have hr : Finset.Icc 1 N \ {1, b - 1, b} =
      (((Finset.Icc 1 N).erase 1).erase (b - 1)).erase (b - 1 + 1) := by
    ext x
    simp [hb1]
    omega
  rw [hr]
  apply erase_two_pairs_even
  · simp; omega
  · simp; omega
  · simp; omega
  · simpa [hr] using hc
  · have hne : c + 1 ≠ c := by omega
    exact Finset.mem_erase.mpr ⟨hne, by simpa [hr] using hc1⟩
  · rw [sum_Icc_one]
    exact Nat.even_iff.mp he

/-- Both adjacent-hole initial effective totals are even. -/
theorem adjacent_hole_effective_totals_even (N b y : ℕ) (hN : 11 ≤ N)
    (hb : 3 ≤ b) (hbN : b ≤ N) (he : Even (N * (N + 1) / 2))
    (hm : y - 1 ∈ Finset.Icc 1 N \ {1, b - 1, b})
    (hy : y ∈ Finset.Icc 1 N \ {1, b - 1, b})
    (hp : y + 1 ∈ Finset.Icc 1 N \ {1, b - 1, b}) :
    (1 + (((Finset.Icc 1 N \ {1, b - 1, b}).erase (y - 1)).erase y).sum
      (fun x ↦ x)) % 2 = 0 ∧
    (1 + (((Finset.Icc 1 N \ {1, b - 1, b}).erase y).erase (y + 1)).sum
      (fun x ↦ x)) % 2 = 0 := by
  have hy1 : y - 1 + 1 = y := by
    have hh := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hy).1).1
    omega
  constructor
  · simpa [hy1] using punctured_neighbor_pair_even N b (y - 1) hN hb hbN he hm
      (by simpa [hy1] using hy)
  · exact punctured_neighbor_pair_even N b y hN hb hbN he hy hp
end CatchUp

namespace CatchUp.ScoreDebtRepair

private def legalPicks : GamePosition → List ℕ → Bool
  | _, [] => true
  | p, x :: xs => decide (¬p.IsTerminal) && decide (x ∈ p.remaining) &&
      legalPicks (p.afterPick x) xs

private theorem legal_picks_sound (p : GamePosition) (xs : List ℕ)
    (h : legalPicks p xs = true) : GamePosition.PickTrace p xs (p.afterPicks xs) := by
  induction xs generalizing p with
  | nil => exact GamePosition.PickTrace.nil p
  | cons x xs ih =>
    simp only [legalPicks, Bool.and_eq_true, decide_eq_true_eq] at h
    exact GamePosition.PickTrace.cons _ _ _ _
      (p.step_after_pick x h.1.1 h.1.2) (ih _ h.2)

/-- The mandatory actual prefix reaches the parametric repair at parameter two. -/
theorem mandatory_actual_prefix :
    GamePosition.PickTrace ⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ [2, 5, 11]
      (actualRoot 2) := by
  have h := legal_picks_sound ⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ [2, 5, 11]
    (by decide +kernel)
  have he : (⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ : GamePosition).afterPicks
      [2, 5, 11] = actualRoot 2 := by decide +kernel
  exact he ▸ h

/-- The legal shadow prefix reaches the matching repair position. -/
theorem mandatory_shadow_prefix :
    GamePosition.PickTrace ⟨AdjacentHoleExchange.exchangeRight,.p1⟩ [5, 2, 7, 11]
      (shadowRoot 2) := by
  have h := legal_picks_sound ⟨AdjacentHoleExchange.exchangeRight,.p1⟩ [5, 2, 7, 11]
    (by decide +kernel)
  have he : (⟨AdjacentHoleExchange.exchangeRight,.p1⟩ : GamePosition).afterPicks
      [5, 2, 7, 11] = shadowRoot 2 := by decide +kernel
  exact he ▸ h

/-- The protected bridge move eleven is forced by any strictly winning strategy. -/
theorem shadow_bridge_forced (x : ℕ)
    (hx : (⟨⟨{6, 10, 11}, 5⟩, .p1⟩ : GamePosition).LegalMove x)
    (hw : ¬CanAvoidLoss .p2
      ((⟨⟨{6, 10, 11}, 5⟩, .p1⟩ : GamePosition).afterPick x)) : x = 11 := by
  have hc : ∀ z : {z // z ∈ ({6, 10, 11} : Finset ℕ)},
      CatchUpSearch.CanAvoidLossClassifier.check .p2
        ((⟨⟨{6, 10, 11}, 5⟩, .p1⟩ : GamePosition).afterPick z) =
          decide (z.val ≠ 11) := by decide +kernel
  by_contra hn
  apply hw
  apply (CatchUpSearch.CanAvoidLossClassifier.check_eq_true_iff _ _).mp
  rw [hc ⟨x, hx⟩]
  exact decide_eq_true hn

/-- Copying the common counter six at the repaired synchronization breaks the margin bound. -/
theorem copied_suffix_margin_obstruction :
    GamePosition.PickTrace (actualRoot 2) [6, 9, 10]
      ((actualRoot 2).afterPicks [6, 9, 10]) ∧
    GamePosition.PickTrace (shadowRoot 2) [6, 10]
      ((shadowRoot 2).afterPicks [6, 10]) ∧
    ((actualRoot 2).afterPicks [6, 9, 10]).IsTerminal ∧
    ((shadowRoot 2).afterPicks [6, 10]).IsTerminal ∧
    ((actualRoot 2).afterPicks [6, 9, 10]).completedMargin .p1 = 2 ∧
    ((shadowRoot 2).afterPicks [6, 10]).completedMargin .p1 = 10 ∧
    ¬((shadowRoot 2).afterPicks [6, 10]).completedMargin .p1 - 2 ≤
      ((actualRoot 2).afterPicks [6, 9, 10]).completedMargin .p1 := by
  refine ⟨legal_picks_sound _ _ (by decide +kernel),
    legal_picks_sound _ _ (by decide +kernel), ?_⟩
  decide +kernel

/-- Extending the terminal max policy back to the mandatory root loses on a legal branch. -/
theorem global_max_policy_obstruction :
    GamePosition.PickTrace ⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ [2, 11, 10, 5, 9, 6]
      ((⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ : GamePosition).afterPicks [2, 11, 10, 5, 9, 6]) ∧
    GreedyPicks ((⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ : GamePosition).afterPick 2)
      [11, 10, 5, 9, 6] ∧
    ((⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ : GamePosition).afterPicks
      [2, 11, 10, 5, 9, 6]).IsTerminal ∧
    ((⟨AdjacentHoleExchange.exchangeLeft,.p1⟩ : GamePosition).afterPicks
      [2, 11, 10, 5, 9, 6]).completedMargin .p1 = -2 := by
  refine ⟨legal_picks_sound _ _ (by decide +kernel), ?_⟩
  simp only [GreedyPicks, Greedy, GamePosition.LegalMove]
  decide +kernel

end CatchUp.ScoreDebtRepair
