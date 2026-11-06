/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/ConsecutiveGuardDescent.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.DeficitCrossing

/-!
# Large winning picks require a reentry at least four labels higher

For the actual support `{3,4} ∪ Icc 9 N` at deficit one, a winning pick `q ≥ 14`
would force a winning opening of the residual support above `q+3`. Consequently,
the top four available tail labels cannot win. Every completed opponent turn is
covered; the proof uses no parity assumption or conjectural draw claim.

The residual opening is not promoted back to a winning pick of the original
support, so these results do not assert infinite descent or nonwinning value.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.ConsecutiveGuardDescent


private theorem turn_small (C Y : Finset ℕ) (c final : ℕ)
    (hmin : ∀ x ∈ C, 3 ≤ x) (hc : c ≤ 4)
    (turn : TurnSet ⟨⟨C,c⟩,.p1⟩ Y final) :
    Y = {final} ∨ (c = 4 ∧ Y = {3,final} ∧ final ≠ 3) := by
  rcases turn.preparation_below with hs | hp
  · exact Or.inl hs
  · have heach : ∀ x ∈ Y.erase final, x = 3 := by
      intro x hx
      have hlo := hmin x (turn.chosen_subset (mem_of_mem_erase hx))
      have hs := single_le_sum (f := fun x : ℕ ↦ x) (fun _ _ ↦ Nat.zero_le _) hx
      change x ≤ (Y.erase final).sum (fun x ↦ x) at hs
      change (Y.erase final).sum (fun x ↦ x) < c at hp
      omega
    by_cases h3 : 3 ∈ Y.erase final
    · have herase : Y.erase final = {3} := eq_singleton_iff_unique_mem.mpr ⟨h3, heach⟩
      simp only [herase, sum_singleton] at hp
      refine Or.inr ⟨by omega, ?_, Ne.symm (mem_erase.mp h3).1⟩
      simpa only [insert_erase turn.final_mem, Finset.pair_comm]
        using congrArg (insert final) herase
    · refine Or.inl (eq_singleton_iff_unique_mem.mpr ⟨turn.final_mem, ?_⟩)
      intro x hx
      by_contra hn
      exact h3 ((heach x (mem_erase.mpr ⟨hn,hx⟩)) ▸ mem_erase.mpr ⟨hn,hx⟩)

private theorem reserve_nonwin_of_entries (C : Finset ℕ) (b c : ℕ)
    (hb : 13 ≤ b) (hc : 2 ≤ c) (hc4 : c ≤ 4)
    (hmin : ∀ x ∈ C, 3 ≤ x) (hbC : b ∉ C)
    (hb1 : b+1 ∉ C) (hbc : b+c ∉ C)
    (hhigh : (⟨C,b+c⟩ : Position).value = .loss)
    (hsingle : (⟨C,b-c⟩ : Position).value ≠ .loss)
    (hpair : c = 4 → (⟨C \ {3}, b-1⟩ : Position).value ≠ .loss) :
    (⟨insert b C,c⟩ : Position).value ≠ .win := by
  have hsum : b ≤ (insert b C).sum (fun x ↦ x) :=
    single_le_sum (f := fun x : ℕ ↦ x) (fun _ _ ↦ Nat.zero_le _) (by simp)
  apply (Position.value_ne_win_iff_forall_turn_sets ⟨insert b C,c⟩ (by simp)
    (by change ¬(insert b C).sum (fun x ↦ x) < c; omega)).mpr
  intro Y final turn
  have hminI : ∀ x ∈ insert b C, 3 ≤ x := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · omega
    · exact hmin x hx
  have hshape := turn_small (insert b C) Y c final hminI hc4 turn
  by_cases hbY : b ∈ Y
  · rcases hshape with rfl | ⟨rfl,rfl,hne⟩
    · have he : final = b := (mem_singleton.mp hbY).symm
      simpa [completedTurnEndpoint,he,sdiff_singleton_eq_erase,hbC] using hsingle
    · have he : final = b := by
        simp only [mem_insert,mem_singleton] at hbY
        omega
      have hset : insert b C \ {3,b} = C \ {3} := by
        ext x
        by_cases hx : x=b <;> simp [hx,hbC,and_comm]
      simpa [completedTurnEndpoint, he, hset, show 3 ≠ b by omega,
        show 3+b-4 = b-1 by omega] using hpair rfl
  · have htotal : Y.sum (fun x ↦ x) ≠ b+c := by
      intro htotal
      have hf := turn.chosen_subset turn.final_mem
      have hfC : final ∈ C :=
        (mem_insert.mp hf).resolve_left (fun he ↦ hbY (he ▸ turn.final_mem))
      rcases hshape with hs | ⟨rfl,hs,hne⟩
      · simp only [hs,sum_singleton] at htotal
        exact hbc (htotal ▸ hfC)
      · have ht : 3+final=b+4 := by simpa [hs,Ne.symm hne] using htotal
        exact hb1 ((show final=b+1 by omega) ▸ hfC)
    have hw := PairEntranceShadow.endpoint_win_of_total_ne C Y b c final
      hbC hhigh turn hbY htotal
    change (completedTurnEndpoint ⟨⟨insert b C,c⟩,.p1⟩ Y).toPosition.value ≠ .loss
    rw [PairEntranceShadow.reserve_endpoint_eq C Y b c hbY,hw]
    decide

private theorem midpoint_single (C : Finset ℕ) (b c : ℕ)
    (hb : 13 ≤ b) (hc : 2 ≤ c) (hc4 : c ≤ 4)
    (h3 : 3 ∈ C) (hb3 : b-3 ∈ C)
    (hhigh : (⟨C,b+c⟩ : Position).value = .loss) :
    (⟨C,b-c⟩ : Position).value ≠ .loss := by
  apply DeficitCrossing.nonloss_of_loss_and_midpoint_turn C {3,b-3}
    (b+c) (b-c) (b-3) hhigh
  · refine ⟨by simp, by simpa only [insert_subset_iff,singleton_subset_iff]
        using (And.intro h3 hb3), ?_, Or.inr ?_⟩
    all_goals norm_num [show 3 ≠ b-3 by omega, erase_insert_of_ne, erase_singleton]
    all_goals omega
  all_goals norm_num [show 3 ≠ b-3 by omega, erase_insert_of_ne, erase_singleton]
  all_goals omega

private theorem midpoint_pair (C : Finset ℕ) (b : ℕ)
    (hb : 13 ≤ b) (h3 : 3 ∈ C) (h4 : 4 ∈ C) (hb4 : b-4 ∈ C)
    (hhigh : (⟨C,b+4⟩ : Position).value = .loss) :
    (⟨C \ {3},b-1⟩ : Position).value ≠ .loss := by
  have hh := PairEntranceShadow.loss_after_subsum C {3} (b+4)
    (singleton_subset_iff.mpr h3) (by simp) hhigh
  have hh' : (⟨C \ {3}, b+1⟩ : Position).value = .loss := by simpa using hh
  apply DeficitCrossing.nonloss_of_loss_and_midpoint_turn (C \ {3}) {4,b-4}
    (b+1) (b-1) (b-4) hh'
  · refine ⟨by simp, ?_, ?_, Or.inr ?_⟩
    · simp [insert_subset_iff,singleton_subset_iff,h4,hb4,show b-4 ≠ 3 by omega]
    all_goals norm_num [show 4 ≠ b-4 by omega, erase_insert_of_ne, erase_singleton]
    all_goals omega
  all_goals norm_num [show 4 ≠ b-4 by omega, erase_insert_of_ne, erase_singleton]
  all_goals omega

/-- Every completed opponent turn is defended using the high losing shadow. -/
theorem small_gap_reserve_nonwin (C : Finset ℕ) (b c : ℕ)
    (hb : 13 ≤ b) (hc : 2 ≤ c) (hc4 : c ≤ 4)
    (hmin : ∀ x ∈ C, 3 ≤ x) (h3 : 3 ∈ C) (h4 : 4 ∈ C)
    (hb3 : b-3 ∈ C) (hb4 : b-4 ∈ C)
    (hbC : b ∉ C) (hb1 : b+1 ∉ C) (hbc : b+c ∉ C)
    (hhigh : (⟨C,b+c⟩ : Position).value = .loss) :
    (⟨insert b C,c⟩ : Position).value ≠ .win := by
  apply reserve_nonwin_of_entries C b c hb hc hc4 hmin hbC hb1 hbc hhigh
  · exact midpoint_single C b c hb hc hc4 h3 hb3 hhigh
  · intro he
    subst c
    exact midpoint_pair C b hb h3 h4 hb4 hhigh


/-- The consecutive-tail endpoint after the defender's first counter two. -/
def support (N : ℕ) : Finset ℕ := {3,4} ∪ Icc 9 N

/-- Delete the tested first counter and its exact deficit. -/
def residual (N q : ℕ) : Finset ℕ := (support N).erase q \ {q-1}

/-- The first three possible larger reentry openings are excluded, with every reply retained. -/
theorem reentry_gap (N q w : ℕ) (hq : 14 ≤ q) (hqN : q ≤ N)
    (hw : w ∈ residual N q) (hqw : q < w)
    (hparent : (⟨(support N).erase q,q-1⟩ : Position).value = .loss)
    (hshadow : (afterOpening (residual N q) w).value = .loss) :
    q+4 ≤ w := by
  by_contra hgap
  let C := (residual N q).erase w
  have hbc : q-1 + (w-(q-1)) = w := by omega
  have hC (x : ℕ) :
      x ∈ C ↔ x ≠ w ∧ (x ≠ q ∧ (x=3 ∨ x=4 ∨ 9 ≤ x ∧ x ≤ N)) ∧ x ≠ q-1 := by
    simp [C,residual,support]
  have hn : (⟨insert (q-1) C,w-(q-1)⟩ : Position).value ≠ .win := by
    apply small_gap_reserve_nonwin C (q-1) (w-(q-1)) (by omega) (by omega) (by omega)
    all_goals try (simp [hC] <;> omega)
    simpa only [hbc,C,afterOpening] using hshadow
  have hset : insert (q-1) C = ((support N).erase q).erase w := by
    ext x
    simp only [C,residual,support,mem_insert,mem_erase,mem_sdiff,mem_singleton,
      mem_union,mem_Icc]
    omega
  have ht : TurnSet ⟨⟨(support N).erase q,q-1⟩,.p1⟩ {w} w :=
    ⟨by simp, singleton_subset_iff.mpr (mem_sdiff.mp hw).1,
      by simp; omega, Or.inl rfl⟩
  have hv := PairEntranceShadow.turn_endpoint_win_of_loss
    ⟨(support N).erase q,q-1⟩ {w} w ht hparent
  exact hn (by simpa only [completedTurnEndpoint,sdiff_singleton_eq_erase,
    sum_singleton,hset] using hv)

/-- A losing child above fourteen must have a genuine reentry at least four labels higher. -/
theorem losing_child_reentry (N q : ℕ) (hq : 14 ≤ q) (hqN : q ≤ N)
    (hparent : (⟨(support N).erase q,q-1⟩ : Position).value = .loss) :
    ∃ w ∈ residual N q, q+4 ≤ w ∧
      (afterOpening (residual N q) w).value = .loss := by
  have hb : q-1 ∈ (support N).erase q := by simp [support]; omega
  obtain ⟨w, hw, hl, hgt⟩ :=
    Position.exists_winning_opening_gt_max_of_loss_of_exact_sum
      ((support N).erase q) {q-1} (q-1) (by simp)
      (by intro x hx; simp only [mem_singleton] at hx; omega)
      (singleton_subset_iff.mpr hb) (by simp) hparent
  have hqw : q < w := by
    have hne := (mem_erase.mp (mem_sdiff.mp hw).1).1
    simp only [max'_singleton] at hgt
    omega
  exact ⟨w,hw,reentry_gap N q w hq hqN hw hqw hparent hl,hl⟩

/-- A winning large first counter must leave room for a reentry four labels higher. -/
theorem winning_pick_bound (N q : ℕ) (hq : 14 ≤ q) (hqN : q ≤ N)
    (hwin : (⟨support N,1⟩ : Position).moveOutcome q = .win) :
    q+4 ≤ N := by
  have hl : (⟨(support N).erase q,q-1⟩ : Position).value = .loss := by
    simp only [Position.moveOutcome, Position.afterPick, show ¬q<1 by omega, ite_false] at hwin
    cases hv : (⟨(support N).erase q,q-1⟩ : Position).value <;> simp_all [Outcome.neg]
  obtain ⟨w,hw,hgap,_⟩ := losing_child_reentry N q hq hqN hl
  simp only [residual,support,mem_sdiff,mem_erase,mem_union,mem_insert,
    mem_singleton,mem_Icc] at hw
  omega

/-- The top four available tail labels cannot win at unit deficit. -/
theorem top_four_pick_nonwin (N q : ℕ) (hq : 14 ≤ q) (hqN : q ≤ N)
    (htop : N < q+4) :
    (⟨support N,1⟩ : Position).moveOutcome q ≠ .win := by
  intro hwin
  exact (Nat.not_le_of_gt htop) (winning_pick_bound N q hq hqN hwin)

end CatchUp.ConsecutiveGuardDescent
