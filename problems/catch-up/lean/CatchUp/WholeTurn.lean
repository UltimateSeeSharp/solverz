/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/WholeTurn.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did); module doc-string added from their results/modules.md.
-/
module

public import Mathlib
public import CatchUp.CompletedTurn
public import CatchUp.PairClassification
public import CatchUp.SevenPairTest

/-!
# WholeTurn

Score-sum draw leaves, balanced-turn defenses and certified failures of proposed one-turn repairs.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open CatchUp
open CatchUpSearch.TopFourClassification (value_eq_draw_iff)
namespace CatchUp.WholeTurn
/-- If all remaining counters exactly fill the deficit, every play finishes tied. -/
theorem sum_draw (S : Finset ℕ) : Position.value ⟨S,S.sum (fun x => x)⟩ = .draw := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases he : S = ∅
    · subst S; simp [Position.value.eq_def]
    · have hm (x : ℕ) (hx : x ∈ S) :
          (Position.mk S (S.sum (fun x => x))).moveOutcome x = .draw := by
        have hs : (S.erase x).sum (fun x => x) + x = S.sum (fun x => x) :=
          Finset.sum_erase_add S (fun x => x) hx
        have hc := ih (S.erase x) (Finset.erase_ssubset hx)
        by_cases hl : x < S.sum (fun x => x)
        · simpa only [Position.moveOutcome, Position.afterPick, hl, ite_true, ite_false,
            show S.sum (fun x => x) - x = (S.erase x).sum (fun x => x) by omega] using hc
        · have hz : x - S.sum (fun x => x) = (S.erase x).sum (fun x => x) := by omega
          simp only [Position.moveOutcome, Position.afterPick, hl, ite_false, hz, hc, Outcome.neg]
      apply (value_eq_draw_iff ⟨S,S.sum (fun x => x)⟩ he (by simp)).mpr
      obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
      exact ⟨⟨x,hx,by rw [hm x hx]; decide⟩,
        fun y hy => by rw [hm y hy]; decide⟩

/-- A legal turn taking the mover's exact remaining draw quota leaves a draw. -/
theorem balanced_endpoint {p : GamePosition} {A : Finset ℕ} {f : ℕ}
    (turn : TurnSet p A f)
    (h : 2 * A.sum (fun x => x) = p.remaining.sum (fun x => x) + p.deficit) :
    (completedTurnEndpoint p A).toPosition.value = .draw := by
  have hs := Finset.sum_sdiff (f := fun x : ℕ => x) turn.chosen_subset
  have hc := turn.catches
  have hd : (p.remaining \ A).sum (fun x => x) =
      A.sum (fun x => x) - p.deficit := by omega
  change Position.value ⟨p.remaining \ A,A.sum (fun x => x)-p.deficit⟩ = .draw
  rw [← hd]
  exact sum_draw _

/-- A balanced legal completed turn guarantees non-loss, not necessarily optimal draw. -/
theorem balanced_turn_safe {p : GamePosition} {A : Finset ℕ} {f : ℕ}
    (turn : TurnSet p A f)
    (h : 2 * A.sum (fun x => x) = p.remaining.sum (fun x => x) + p.deficit) :
    CanAvoidLoss p.toMove p := by
  obtain ⟨preparation,trace,_⟩ :=
    (exists_completed_turn_iff_turn_set p (completedTurnEndpoint p A) A f).mpr ⟨turn,rfl⟩
  apply trace.can_avoid_loss_of_safe_endpoint rfl
  rw [can_avoid_loss_iff_value]
  have hd := balanced_endpoint turn h
  split <;> rw [hd] <;> decide

/-- Select uppers exactly on U and lowers on the other intact pairs. -/
def preparation (B U : Finset ℕ) : Finset ℕ :=
  (B \ U) ∪ U.image (fun b => b+1)

private theorem even_disjoint (B U : Finset ℕ)
    (hB : ∀ b ∈ B, b%2=0) (hU : U ⊆ B) :
    Disjoint B (U.image (fun b => b+1)) := by
  rw [Finset.disjoint_left]
  intro b hb hi
  rcases Finset.mem_image.mp hi with ⟨u,hu,he⟩
  have hbe := hB b hb
  have hue := hB u (hU hu)
  omega

theorem paired_eq_union (B : Finset ℕ) :
    SevenPairTest.pairedCounters B = B ∪ B.image (fun b => b+1) := by
  ext x
  simp only [SevenPairTest.pairedCounters, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨a,ha,h | h⟩
    · exact Or.inl (h ▸ ha)
    · exact Or.inr ⟨a,ha,h.symm⟩
  · rintro (hx | ⟨a,ha,h⟩)
    · exact ⟨x,hx,Or.inl rfl⟩
    · exact ⟨a,ha,Or.inr h.symm⟩

theorem sum_preparation (B U : Finset ℕ)
    (hB : ∀ b ∈ B, b%2=0) (hU : U ⊆ B) :
    (preparation B U).sum (fun x => x) = B.sum (fun x => x) + U.card := by
  have hd : Disjoint (B \ U) (U.image (fun b => b+1)) :=
    (even_disjoint B U hB hU).mono_left Finset.sdiff_subset
  rw [preparation, Finset.sum_union hd, Finset.sum_image]
  · have hs := Finset.sum_sdiff (f := fun x : ℕ => x) hU
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  · intro x hx y hy h
    dsimp at h
    omega

theorem sum_pairs (B : Finset ℕ) (hB : ∀ b ∈ B, b%2=0) :
    (SevenPairTest.pairedCounters B).sum (fun x => x) =
      2 * B.sum (fun x => x) + B.card := by
  rw [paired_eq_union, Finset.sum_union (even_disjoint B B hB (by rfl)),
    Finset.sum_image]
  · simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  · intro x hx y hy h
    dsimp at h
    omega

/-- Arbitrary pair count: choose U's uppers and the other lowers, then the orphan.
The count equation balances the quota; the strict sum bound prevents an early catch. -/
theorem orphan_balance (B U H : Finset ℕ) (z d e : ℕ) (player : Player)
    (hB : ∀ b ∈ B, b%2=0) (hU : U ⊆ B)
    (hH : Disjoint H (SevenPairTest.pairedCounters B))
    (hz : z ∉ H ∪ SevenPairTest.pairedCounters B)
    (hgap : d+e=z)
    (hcount : H.sum (fun x => x)+B.card=e+2*U.card)
    (hbelow : B.sum (fun x => x)+U.card<d) :
    let p : GamePosition := ⟨⟨insert z (H ∪ SevenPairTest.pairedCounters B),d⟩,player⟩
    let A := insert z (preparation B U)
    TurnSet p A z ∧
      (completedTurnEndpoint p A).toPosition.value = .draw ∧
      CanAvoidLoss player p := by
  dsimp only
  have hsub : preparation B U ⊆ SevenPairTest.pairedCounters B := by
    rw [paired_eq_union]
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1
    · rcases Finset.mem_image.mp hx with ⟨b,hb,rfl⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hU hb,rfl⟩)
  have hzP : z ∉ preparation B U := by
    intro hm
    exact hz (Finset.mem_union_right _ (hsub hm))
  have hP := sum_preparation B U hB hU
  have hR : (insert z (H ∪ SevenPairTest.pairedCounters B)).sum (fun x => x) =
      z + H.sum (fun x => x) + 2*B.sum (fun x => x) + B.card := by
    rw [Finset.sum_insert hz, Finset.sum_union hH, sum_pairs B hB]
    omega
  have hA : (insert z (preparation B U)).sum (fun x => x) =
      z+B.sum (fun x => x)+U.card := by
    rw [Finset.sum_insert hzP,hP]
    omega
  have turn : TurnSet
      ⟨⟨insert z (H ∪ SevenPairTest.pairedCounters B),d⟩,player⟩
      (insert z (preparation B U)) z := by
    constructor
    · exact Finset.mem_insert_self _ _
    · exact Finset.insert_subset_insert z (fun x hx => Finset.mem_union_right _ (hsub hx))
    · change d ≤ (insert z (preparation B U)).sum (fun x => x)
      rw [hA]
      omega
    · right
      change ((insert z (preparation B U)).erase z).sum (fun x => x) < d
      rw [Finset.erase_insert hzP,hP]
      exact hbelow
  have hbalanced : 2 * (insert z (preparation B U)).sum (fun x => x) =
      (insert z (H ∪ SevenPairTest.pairedCounters B)).sum (fun x => x) + d := by
    rw [hA,hR]
    omega
  exact ⟨turn,balanced_endpoint turn hbalanced,balanced_turn_safe turn hbalanced⟩

/-- In the singleton-five residual after an opponent's large lower pick r,
four plus twice |U| intact pairs admit a draw-guaranteeing whole-turn reply.
This covers four, six, eight, ... pairs without enumerating game trees. -/
theorem far_lower_safe (B U : Finset ℕ) (r : ℕ) (player : Player)
    (hB : ∀ b ∈ B, 6≤b ∧ b%2=0) (hU : U ⊆ B)
    (hcount : B.card=4+2*U.card)
    (hfar : B.sum (fun x => x)+U.card+8<r) :
    let p : GamePosition :=
      ⟨⟨insert (r+1) (insert 5 (SevenPairTest.pairedCounters B)),r-8⟩,player⟩
    let A := insert (r+1) (preparation B U)
    TurnSet p A (r+1) ∧
      (completedTurnEndpoint p A).toPosition.value = .draw ∧
      CanAvoidLoss player p := by
  have hp : ∀ b ∈ B, b%2=0 := fun b hb => (hB b hb).2
  have hnot5 : 5 ∉ SevenPairTest.pairedCounters B := by
    rw [paired_eq_union]
    simp only [Finset.mem_union, Finset.mem_image, not_or]
    constructor
    · intro hb
      have := (hB 5 hb).1
      omega
    · rintro ⟨b,hb,he⟩
      have := (hB b hb).1
      omega
  have hr : r+1 ∉ ({5} : Finset ℕ) ∪ SevenPairTest.pairedCounters B := by
    rw [paired_eq_union]
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image, not_or]
    refine ⟨by omega,?_,?_⟩
    · intro hb
      have hle := Finset.single_le_sum (fun y _ => Nat.zero_le y) hb
      omega
    · rintro ⟨b,hb,he⟩
      have hle := Finset.single_le_sum (fun y _ => Nat.zero_le y) hb
      omega
  have hh : Disjoint ({5} : Finset ℕ) (SevenPairTest.pairedCounters B) := by
    simpa using hnot5
  simpa only [Finset.singleton_union, Finset.sum_singleton] using
    orphan_balance B U {5} (r+1) (r-8) 9 player hp hU hh hr
      (by omega) (by simpa using (show 5+B.card=9+2*U.card by omega)) (by omega)

/-- The far-orphan defense needs no supplied subset: its size determines one. -/
theorem far_lower_nonloss (B : Finset ℕ) (t r : ℕ)
    (hB : ∀ b ∈ B, 6≤b ∧ b%2=0)
    (hcount : B.card=4+2*t)
    (hfar : B.sum (fun x => x)+t+8<r) :
    Position.value
      ⟨insert (r+1) (insert 5 (SevenPairTest.pairedCounters B)),r-8⟩ ≠ .loss := by
  obtain ⟨U,hU,hcard⟩ := Finset.exists_subset_card_eq (show t≤B.card by omega)
  have hs := (far_lower_safe B U r .p1 hB hU (by omega) (by omega)).2.2
  simpa only [can_avoid_loss_iff_value, ite_eq_left rfl, ↓reduceIte] using hs

/-- Necessary size condition for balancing the entire remaining score in one legal turn.
It is stronger than a partition-sum check because it uses immediate turn stopping. -/
theorem balanced_turn_total_bound {p : GamePosition} {A : Finset ℕ} {f M : ℕ}
    (turn : TurnSet p A f) (hd : 0<p.deficit)
    (hM : ∀ x ∈ p.remaining, x≤M)
    (hb : 2*A.sum (fun x => x)=p.remaining.sum (fun x => x)+p.deficit) :
    p.remaining.sum (fun x => x)<p.deficit+2*M := by
  have hf := hM f (turn.chosen_subset turn.final_mem)
  have hs : A.sum (fun x => x)<p.deficit+M := by
    rcases turn.preparation_below with he | hl
    · rw [he,Finset.sum_singleton]
      omega
    · have he := Finset.sum_erase_add A (fun x => x) turn.final_mem
      omega
  omega

/-- No one-turn score-balancing repair can apply at the certified mate obstruction. -/
theorem critical_not_balanced :
    ¬∃ A f, TurnSet SevenPairTest.beforeBadMate A f ∧
      2*A.sum (fun x => x)=
        SevenPairTest.beforeBadMate.remaining.sum (fun x => x)+
          SevenPairTest.beforeBadMate.deficit := by
  rintro ⟨A,f,turn,hb⟩
  have h := balanced_turn_total_bound turn (by decide +kernel)
    (M:=41) (by change ∀ x ∈ ({5,6,7,10,11,13,20,21,40,41}:Finset ℕ), x≤41
                decide +kernel) hb
  have hn : ¬SevenPairTest.beforeBadMate.remaining.sum (fun x => x)<
      SevenPairTest.beforeBadMate.deficit+2*41 := by decide +kernel
  exact hn h

/-- If the total exceeds the deficit but all counters except f still fall short,
the mover can take everything in one legal turn and win. -/
theorem win_of_all_turn (S : Finset ℕ) (d f : ℕ) (hf : f∈S)
    (hwin : d<S.sum (fun x => x))
    (hbelow : (S.erase f).sum (fun x => x)<d) :
    Position.value ⟨S,d⟩ = .win := by
  have turn : TurnSet ⟨⟨S,d⟩,.p1⟩ S f :=
    ⟨hf,Finset.Subset.refl _,Nat.le_of_lt hwin,Or.inr hbelow⟩
  by_contra hn
  have hs := (Position.value_ne_win_iff_forall_turn_sets ⟨S,d⟩
    (Finset.nonempty_iff_ne_empty.mp ⟨f,hf⟩)
      (by change ¬S.sum (fun x => x)<d; omega)).mp hn S f turn
  have he : (completedTurnEndpoint ⟨⟨S,d⟩,.p1⟩ S).toPosition.value = .loss := by
    change Position.value ⟨S \ S,S.sum (fun x => x)-d⟩ = .loss
    rw [Finset.sdiff_self,Position.value.eq_def]
    simp [show S.sum (fun x => x)-d≠0 by omega]
  exact hs he

/-- The uncorrected all-lower reply in the nine-pair test leaves a strict win
for the new mover: the remaining total is 179, and its deficit is only 177. -/
theorem nine_uncorrected_endpoint_win :
    Position.value ⟨{5,7,11,13,21,41,81},177⟩ = .win := by
  exact win_of_all_turn _ 177 81 (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- The count-corrected response for six intact pairs chooses exactly one upper.
Its endpoint draws, and it guarantees safety for the responding player. -/
theorem nine_corrected :
    let p : GamePosition :=
      ⟨⟨insert 181 (insert 5 (SevenPairTest.pairedCounters {6,10,12,20,40,80})),172⟩,.p2⟩
    let A := insert 181 (preparation {6,10,12,20,40,80} {6})
    TurnSet p A 181 ∧
      (completedTurnEndpoint p A).toPosition.value = .draw ∧
      CanAvoidLoss .p2 p := by
  exact far_lower_safe {6,10,12,20,40,80} {6} 180 .p2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The uncorrected nine-pair reply really is one legal turn; no early catch
or illegal swap explains its failure. The new mover then has the win above. -/
theorem nine_uncorrected_turn :
    CompletedTurn
      ⟨⟨{5,6,7,10,11,12,13,20,21,40,41,80,81,181},172⟩,.p2⟩
      [6,10,12,20,40,80,181]
      ⟨⟨{5,7,11,13,21,41,81},177⟩,.p1⟩ := by
  have h := completed_turn_of_preparation
    ⟨⟨{5,6,7,10,11,12,13,20,21,40,41,80,81,181},172⟩,.p2⟩
    [6,10,12,20,40,80] 181
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have he : completedTurnEndpoint
      ⟨⟨{5,6,7,10,11,12,13,20,21,40,41,80,81,181},172⟩,.p2⟩
      (insert 181 [6,10,12,20,40,80].toFinset) =
      ⟨⟨{5,7,11,13,21,41,81},177⟩,.p1⟩ := by decide +kernel
  rw [he] at h
  exact h

/-- A large total rules out a one-turn exact-quota reply after EVERY opening.
This only refutes that shortcut strategy, not the existence of a multi-turn defense. -/
theorem no_balance_after_opening (S : Finset ℕ) (x M : ℕ)
    (hx : x∈S) (hpos : 0<x) (hM : ∀ y∈S,y≤M)
    (htotal : 4*M≤S.sum (fun y => y)) :
    ¬∃ A f, TurnSet ⟨⟨S.erase x,x⟩,.p2⟩ A f ∧
      2*A.sum (fun y => y)=(S.erase x).sum (fun y => y)+x := by
  rintro ⟨A,f,turn,hb⟩
  have hs := balanced_turn_total_bound turn hpos
    (fun y hy => hM y (Finset.mem_erase.mp hy).2) hb
  have he := Finset.sum_erase_add S (fun y => y) hx
  have hxm := hM x hx
  try simp only at he hs
  omega

private theorem four_mul_le_interval_sum (N : ℕ) (hN : 7≤N) :
    4*N≤(Finset.Icc 1 N).sum (fun x => x) := by
  induction N,hN using Nat.le_induction with
  | base => decide +kernel
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    omega

/-- For all initial intervals N>=7 and every legal opening, the second player
cannot take its entire remaining draw quota in its first turn.
This includes every substantive eligible interval from N=7 onward. -/
theorem interval_no_one_turn_balance (N x : ℕ) (hN : 7≤N)
    (hx : x∈Finset.Icc 1 N) :
    ¬∃ A f, TurnSet ⟨⟨(Finset.Icc 1 N).erase x,x⟩,.p2⟩ A f ∧
      2*A.sum (fun y => y)=((Finset.Icc 1 N).erase x).sum (fun y => y)+x := by
  exact no_balance_after_opening _ x N hx (by have := (Finset.mem_Icc.mp hx).1; omega)
    (fun y hy => (Finset.mem_Icc.mp hy).2) (four_mul_le_interval_sum N hN)
end CatchUp.WholeTurn
