/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/IntervalReserveDepth.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.WholeTurn
public import CatchUp.TurnDepth

/-!
# Closure-depth barriers for the actual interval reserve endpoints

Every allowed opponent counter, including seven, is retained. The estimates
exclude a one-turn balanced-quota repair from N twelve onward and bound
arbitrary legal completed-turn chains reaching a terminal or score-sum leaf.
They prove neither a strategy nor a lower bound on formal proof size. No
conversion of arbitrary raw atomic paths to completed-turn chains is asserted.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.IntervalReserveDepth

/-- The actual reserve support before the opponent's allowed singleton pick. -/
def reserve (N : ℕ) : Finset ℕ := insert 7 (Icc 9 N)

/-- The remaining endpoint, from either possible acting player's perspective. -/
def start (N y : ℕ) (player : Player) : GamePosition :=
  ⟨⟨(reserve N).erase y, y - 3⟩, player⟩

private theorem reserve_subset (N : ℕ) (hN : 7 ≤ N) : reserve N ⊆ Icc 1 N := by
  intro x hx
  rcases mem_insert.mp hx with rfl | hx
  · exact mem_Icc.mpr ⟨by omega, hN⟩
  · have hi := mem_Icc.mp hx
    exact mem_Icc.mpr ⟨by omega, hi.2⟩

private theorem reserve_min (N y : ℕ) (hy : y ∈ reserve N) : 7 ≤ y := by
  rcases mem_insert.mp hy with rfl | hy
  · omega
  · exact (mem_Icc.mp hy).1.trans' (by omega)

private theorem tail_sum_identity (N : ℕ) (hN : 8 ≤ N) :
    (Icc 9 N).sum id + 36 = (Icc 1 N).sum id := by
  induction N, hN using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      change (Icc 9 n).sum id + (n + 1) + 36 = (Icc 1 n).sum id + (n + 1)
      omega

/-- Erasing the allowed counter accounts for twenty-nine units of missing low-label mass. -/
theorem start_mass (N y : ℕ) (player : Player) (hN : 8 ≤ N)
    (hy : y ∈ reserve N) :
    (start N y player).remaining.sum id + y + 29 = (Icc 1 N).sum id := by
  have htail := tail_sum_identity N hN
  have hreserve : (reserve N).sum id = 7 + (Icc 9 N).sum id := by
    unfold reserve
    rw [sum_insert (by simp)]
    rfl
  have herase := sum_erase_add (reserve N) (fun x : ℕ ↦ x) hy
  change ((reserve N).erase y).sum id + y = (reserve N).sum id at herase
  change ((reserve N).erase y).sum id + y + 29 = (Icc 1 N).sum id
  omega

private theorem start_deficit (N y : ℕ) (player : Player) (hy : y ∈ reserve N) :
    (start N y player).deficit + 3 = y := by
  have hlo := reserve_min N y hy
  change y - 3 + 3 = y
  omega

private theorem interval_mass_large (N : ℕ) (hN : 12 ≤ N) :
    4 * N + 26 ≤ (Icc 1 N).sum id := by
  induction N, hN using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
      rw [sum_Icc_succ_top (by omega)]
      change 4 * (n + 1) + 26 ≤ (Icc 1 n).sum id + (n + 1)
      omega

/-- No allowed endpoint has a legal single-turn exact-quota repair when N is at least twelve. -/
theorem no_one_turn_balance (N y : ℕ) (player : Player) (hN : 12 ≤ N)
    (hy : y ∈ reserve N) :
    ¬ ∃ A final, TurnSet (start N y player) A final ∧
      2 * A.sum id = (start N y player).remaining.sum id +
        (start N y player).deficit := by
  rintro ⟨A, final, turn, hbalance⟩
  have hlo := reserve_min N y hy
  have hmass := start_mass N y player (by omega) hy
  have hd := start_deficit N y player hy
  have hlarge := interval_mass_large N hN
  have hyN := (mem_Icc.mp (reserve_subset N (by omega) hy)).2
  have hb := WholeTurn.balanced_turn_total_bound turn
    (by change 0 < y - 3; omega) (M := N)
    (fun x hx ↦ (mem_Icc.mp (reserve_subset N (by omega) (mem_of_mem_erase hx))).2)
    hbalance
  change (start N y player).remaining.sum id <
    (start N y player).deficit + 2 * N at hb
  omega

/-- Any completed-turn chain reaching a terminal or score-sum leaf needs enough final mass. -/
theorem chain_mass_barrier
    (N y : ℕ) (player : Player) (hN : 8 ≤ N) (hy : y ∈ reserve N)
    {finals : List ℕ} {rise : ℕ} {after : GamePosition}
    (chain : TurnDepth.TurnChain (start N y player) finals rise after)
    (hleaf : after.remaining.sum id ≤ after.deficit) :
    (Icc 1 N).sum id ≤ 26 + 2 * (y + finals.sum) := by
  have hmass := start_mass N y player hN hy
  have hd := start_deficit N y player hy
  have hc := chain.conservation
  have hr := chain.rise_le_finals_sum
  change (start N y player).remaining.sum id + after.deficit =
    (start N y player).deficit + 2 * rise + after.remaining.sum id at hc
  omega

/-- A uniform multi-turn depth obstruction, including every allowed opponent counter y. -/
theorem chain_depth_barrier
    (N y : ℕ) (player : Player) (hN : 8 ≤ N) (hy : y ∈ reserve N)
    {finals : List ℕ} {rise : ℕ} {after : GamePosition}
    (chain : TurnDepth.TurnChain (start N y player) finals rise after)
    (hleaf : after.remaining.sum id ≤ after.deficit) :
    N * (N + 1) ≤ 52 + 4 * N * (finals.length + 1) := by
  have hb := chain_mass_barrier N y player hN hy chain hleaf
  have hs := chain.finals_sum_le (M := N)
    (fun x hx ↦ (mem_Icc.mp (reserve_subset N (by omega) (mem_of_mem_erase hx))).2)
  have hyN := (mem_Icc.mp (reserve_subset N (by omega) hy)).2
  have ht := TurnDepth.interval_sum_twice N
  change 2 * (Icc 1 N).sum id = N * (N + 1) at ht
  nlinarith

/-- The erased opening counter and every turn-final counter are distinct interval labels. -/
private theorem opening_finals_nodup
    {N y rise : ℕ} {player : Player} {finals : List ℕ} {after : GamePosition}
    (chain : TurnDepth.TurnChain (start N y player) finals rise after) :
    (y :: finals).Nodup := by
  rw [List.nodup_cons]
  refine ⟨?_, chain.finals_nodup⟩
  intro hy
  have hm := chain.finals_subset_remaining (List.mem_toFinset.mpr hy)
  change y ∈ (reserve N).erase y at hm
  exact (mem_erase.mp hm).1 rfl

private theorem opening_finals_subset
    {N y rise : ℕ} {player : Player} {finals : List ℕ} {after : GamePosition}
    (hN : 7 ≤ N) (hy : y ∈ reserve N)
    (chain : TurnDepth.TurnChain (start N y player) finals rise after) :
    (y :: finals).toFinset ⊆ Icc 1 N := by
  intro x hx
  rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with rfl | hx
  · exact reserve_subset N hN hy
  · exact reserve_subset N hN
      (mem_of_mem_erase (chain.finals_subset_remaining (List.mem_toFinset.mpr hx)))

/-- Distinct turn-final counters sharpen the actual reserve endpoint's closure-depth barrier. -/
theorem chain_depth_sharp
    (N y : ℕ) (player : Player) (hN : 8 ≤ N) (hy : y ∈ reserve N)
    {finals : List ℕ} {rise : ℕ} {after : GamePosition}
    (chain : TurnDepth.TurnChain (start N y player) finals rise after)
    (hleaf : after.remaining.sum id ≤ after.deficit) :
    (Icc 1 N).sum id ≤ 26 + (finals.length + 1) * (2 * N - finals.length) := by
  have hb := chain_mass_barrier N y player hN hy chain hleaf
  have hsub := opening_finals_subset (by omega) hy chain
  have hp := TurnDepth.interval_subset_sum_bound N (y :: finals).toFinset hsub
  have hn := opening_finals_nodup chain
  have hc : (y :: finals).toFinset.card = finals.length + 1 := by
    simpa using List.toFinset_card_of_nodup hn
  have hs : (y :: finals).toFinset.sum (fun x ↦ x) = y + finals.sum := by
    simpa using List.sum_toFinset (fun x : ℕ ↦ x) hn
  have hcard := Finset.card_le_card hsub
  rw [hc, hs] at hp
  rw [hc] at hcard
  have hlen : finals.length + 1 ≤ N := by simpa using hcard
  have hpred : 2 * N - (finals.length + 1) + 1 = 2 * N - finals.length := by omega
  rw [hpred] at hp
  omega

/-- The lower threshold cannot be reduced to eleven: preparation seven, then final ten balances. -/
theorem eleven_balanced_turn (player : Player) :
    TurnSet (start 11 11 player) {7, 10} 10 ∧
      2 * ({7, 10} : Finset ℕ).sum id = (start 11 11 player).remaining.sum id +
        (start 11 11 player).deficit := by
  constructor
  · refine ⟨by decide +kernel, ?_, ?_, Or.inr ?_⟩
    · change {7, 10} ⊆ (reserve 11).erase 11
      decide +kernel
    · change 8 ≤ ({7, 10} : Finset ℕ).sum id
      decide +kernel
    · change (({7, 10} : Finset ℕ).erase 10).sum id < 8
      decide +kernel
  · change 2 * ({7, 10} : Finset ℕ).sum id = ((reserve 11).erase 11).sum id + 8
    decide +kernel

end CatchUp.IntervalReserveDepth
