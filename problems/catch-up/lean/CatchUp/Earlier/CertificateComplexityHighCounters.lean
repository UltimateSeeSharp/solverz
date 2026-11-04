/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CertificateComplexityHighCounters.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.CertificateComplexityGame

/-!
# Exponential full-certificate lower bound using large counters

A completed turn can consume at most two counters above half the interval maximum.
Target-set covering therefore has constant deletion cost in this tracked alphabet.
This concerns explicit atomic DAGs, not symbolic mathematical proof length.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateComplexity

open CatchUp CertificateChecker

/-- The large half of the interval. -/
def largeCounters (N : ℕ) : Finset ℕ := Finset.Icc (N / 2 + 1) N

/-- Large counters still present at a game position. -/
def largeRemaining (N : ℕ) (p : GamePosition) : Finset ℕ := largeCounters N ∩ p.remaining

theorem large_counter_twice_gt (N x : ℕ) (hx : x ∈ largeCounters N) : N < 2 * x := by
  have := (Finset.mem_Icc.mp hx).1
  omega

/-- Two large counters already have total greater than the reachable deficit bound. -/
theorem nonterminal_of_two_large (N : ℕ) (p : GamePosition) (hd : p.deficit ≤ N)
    (hlarge : 2 ≤ (largeRemaining N p).card) : ¬p.IsTerminal := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlarge
  obtain ⟨hxL, hxp⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyL, hyp⟩ := Finset.mem_inter.mp hy
  have hxlarge := large_counter_twice_gt N x hxL
  have hylarge := large_counter_twice_gt N y hyL
  have hsub : {x, y} ⊆ p.remaining := by simp [Finset.insert_subset_iff, hxp, hyp]
  have hsum := Finset.sum_le_sum_of_subset (f := fun z : ℕ => z) hsub
  rw [Finset.sum_pair hxy] at hsum
  try dsimp only at hsum
  rintro (hempty | hlt)
  · simp [hempty] at hxp
  · omega

/-- At most two large counters occur in an uninterrupted completed turn. -/
theorem completed_turn_large_card_le_two (N : ℕ)
    {p q : GamePosition} {xs : List ℕ} (trace : CompletedTurn p xs q)
    (hd : p.deficit ≤ N) : (xs.toFinset ∩ largeCounters N).card ≤ 2 := by
  have hex : ∃ pre last, xs = pre ++ [last] := by
    cases xs using List.reverseRecOn with
    | nil => exact False.elim (trace.picks_nonempty rfl)
    | append_singleton pre last => exact ⟨pre, last, rfl⟩
  obtain ⟨pre, last, rfl⟩ := hex
  have hpre : (pre.toFinset ∩ largeCounters N).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    obtain ⟨hxp, hxL⟩ := Finset.mem_inter.mp hx
    obtain ⟨hyp, hyL⟩ := Finset.mem_inter.mp hy
    have hxlarge := large_counter_twice_gt N x hxL
    have hylarge := large_counter_twice_gt N y hyL
    have hsub : {x, y} ⊆ pre.toFinset := by
      simp [Finset.insert_subset_iff, hxp, hyp]
    have hsum := Finset.sum_le_sum_of_subset (f := fun z : ℕ => z) hsub
    rw [Finset.sum_pair hxy] at hsum
    have hnd : pre.Nodup := (List.nodup_append.mp trace.picks_nodup).1
    have hsumeq : pre.toFinset.sum (fun x : ℕ => x) = pre.sum := by
      simpa using List.sum_toFinset (fun x : ℕ => x) hnd
    rw [hsumeq] at hsum
    rcases trace.preparation_sum_lt_or_empty with he | hlt
    · simp [he] at hxp
    · omega
  have hsub : (pre ++ [last]).toFinset ∩ largeCounters N ⊆
      insert last (pre.toFinset ∩ largeCounters N) := by
    intro x hx
    simp only [Finset.mem_inter, List.mem_toFinset, List.mem_append,
      List.mem_singleton] at hx
    rcases hx.1 with hp | he
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hp, hx.2⟩)
    · exact Finset.mem_insert.mpr (Or.inl he)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  omega

/-- The large-counter count drops by at most two during a completed turn. -/
theorem completed_turn_large_count (N : ℕ) {p q : GamePosition} {xs : List ℕ}
    (trace : CompletedTurn p xs q) (hd : p.deficit ≤ N) :
    (largeRemaining N p).card ≤ (largeRemaining N q).card + 2 := by
  let A := xs.toFinset ∩ largeCounters N
  have hsub : A ⊆ largeRemaining N p := by
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨hx'.2, trace.picks_subset_remaining hx'.1⟩
  have heq : largeRemaining N q = largeRemaining N p \ A := by
    rw [largeRemaining, trace.after_remaining]
    ext x
    simp only [largeRemaining, A, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [← heq] at hc
  have hA := completed_turn_large_card_le_two N trace hd
  change A.card ≤ 2 at hA
  omega

/-- Deleting a picked counter costs at most one tracked large counter. -/
theorem large_count_after_pick (N : ℕ) (p : GamePosition) (x : ℕ) :
    (largeRemaining N p).card ≤ (largeRemaining N (p.afterPick x)).card + 1 := by
  have heq : largeRemaining N (p.afterPick x) = (largeRemaining N p).erase x :=
    Finset.inter_erase x _ _
  rw [heq]
  by_cases hx : x ∈ largeRemaining N p
  · exact (Finset.card_erase_add_one hx).symm.le
  · simp [Finset.erase_eq_of_notMem hx]

/-- Remaining-set inclusion also preserves inclusion of the tracked large counters. -/
theorem largeRemaining_mono (N : ℕ) {p q : GamePosition} (hsub : q.remaining ⊆ p.remaining) :
    largeRemaining N q ⊆ largeRemaining N p := by
  intro x hx
  obtain ⟨hL, hq⟩ := Finset.mem_inter.mp hx
  exact Finset.mem_inter.mpr ⟨hL, hsub hq⟩

/-- An adversarial target pick and the ensuing protected turn cost at most three large counters. -/
theorem large_adversary_macro {dag : StrategyDAG} (hv : DAGValid dag)
    (N : ℕ) (p : GamePosition) (hp : ContainsPosition dag p)
    (hturn : p.toMove ≠ dag.player)
    (hS : p.remaining ⊆ Finset.Icc 1 N) (hd : p.deficit ≤ N)
    (hcard : 5 ≤ (largeRemaining N p).card)
    (x : ℕ) (hx : p.LegalMove x) :
    ∃ q, ContainsPosition dag q ∧ q.toMove ≠ dag.player ∧
      q.remaining ⊆ p.remaining ∧ x ∉ q.remaining ∧
      (largeRemaining N p).card ≤ (largeRemaining N q).card + 3 ∧
      q.remaining ⊆ Finset.Icc 1 N ∧ q.deficit ≤ N := by
  have hnt := nonterminal_of_two_large N p hd (by omega)
  have hchild := opponent_step hv p hp hnt hturn x hx
  have hb := bounded_after_pick N p hS hd x hx
  have hc := large_count_after_pick N p x
  have hchildSub : (p.afterPick x).remaining ⊆ p.remaining := Finset.erase_subset _ _
  have hxnot : x ∉ (p.afterPick x).remaining := Finset.notMem_erase _ _
  by_cases hbehind : x < p.deficit
  · refine ⟨p.afterPick x, hchild, ?_, hchildSub, hxnot, ?_, hb⟩
    · simpa only [GamePosition.to_move_after_pick_of_lt _ _ hbehind] using hturn
    · omega
  · have hchildTurn : (p.afterPick x).toMove = dag.player := by
      rw [GamePosition.to_move_after_pick_of_le _ _ (by omega)]
      exact (Player.other_eq_iff_ne _ _).mpr hturn
    have hchildNt := nonterminal_of_two_large N (p.afterPick x) hb.2 (by omega)
    obtain ⟨xs, q, trace, hq⟩ := owner_completed_turn hv _ hchild hchildNt hchildTurn
    have hcount := completed_turn_large_count N trace hb.2
    have hqSub : q.remaining ⊆ (p.afterPick x).remaining := by
      rw [trace.after_remaining]
      exact Finset.sdiff_subset
    have hqb := bounded_after_trace N trace.pick_trace hb.1 hb.2
    refine ⟨q, hq, ?_, hqSub.trans hchildSub, fun hxq => hxnot (hqSub hxq), ?_, hqb⟩
    · rw [trace.after_to_move, hchildTurn]
      cases dag.player <;> decide
    · omega

/-- Every chosen set of large targets can be erased inside the certificate at a cost
of at most three large counters per target, regardless of protected replies. -/
theorem force_large_target_deletion {dag : StrategyDAG} (hv : DAGValid dag)
    (N : ℕ) (p : GamePosition) (hp : ContainsPosition dag p)
    (hturn : p.toMove ≠ dag.player)
    (hS : p.remaining ⊆ Finset.Icc 1 N) (hd : p.deficit ≤ N)
    (T : Finset ℕ) (hT : T ⊆ largeRemaining N p)
    (hcard : 2 + 3 * T.card ≤ (largeRemaining N p).card) :
    ∃ q, ContainsPosition dag q ∧ q.toMove ≠ dag.player ∧ q.remaining ⊆ p.remaining ∧
      Disjoint T q.remaining ∧
      (largeRemaining N p).card ≤ (largeRemaining N q).card + 3 * T.card := by
  by_cases he : T = ∅
  · subst T
    exact ⟨p, hp, hturn, Finset.Subset.refl _, by simp, by simp⟩
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have htpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨x, hx⟩
    obtain ⟨q, hq, hqturn, hqsub, hxnot, hqcard, hqS, hqd⟩ :=
      large_adversary_macro hv N p hp hturn hS hd (by omega) x
        (Finset.mem_inter.mp (hT hx)).2
    let U := T ∩ q.remaining
    have hUsub : U ⊆ T.erase x := by
      intro y hy
      have hy' := Finset.mem_inter.mp hy
      exact Finset.mem_erase.mpr ⟨by intro heq; subst y; exact hxnot hy'.2, hy'.1⟩
    have hUcard : U.card < T.card :=
      (Finset.card_le_card hUsub).trans_lt (Finset.card_erase_lt_of_mem hx)
    have hUq : U ⊆ largeRemaining N q := by
      intro y hy
      have hy' := Finset.mem_inter.mp hy
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hT hy'.1)).1, hy'.2⟩
    have hbudget : 2 + 3 * U.card ≤ (largeRemaining N q).card := by omega
    obtain ⟨r, hr, hrturn, hrsub, hrdisj, hrcard⟩ :=
      force_large_target_deletion hv N q hq hqturn hqS hqd U hUq hbudget
    refine ⟨r, hr, hrturn, hrsub.trans hqsub, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro y hyT hyr
      exact Finset.disjoint_left.mp hrdisj (Finset.mem_inter.mpr ⟨hyT, hrsub hyr⟩) hyr
    · omega
termination_by T.card
decreasing_by exact hUcard

/-- Constant-cost covering gives an exponential full-DAG bound from an adversary node. -/
theorem large_opponent_node_lower_bound {dag : StrategyDAG} (hv : DAGValid dag)
    (N t : ℕ) (p : GamePosition) (hp : ContainsPosition dag p)
    (hturn : p.toMove ≠ dag.player)
    (hS : p.remaining ⊆ Finset.Icc 1 N) (hd : p.deficit ≤ N)
    (hbudget : 2 + 3 * t ≤ (largeRemaining N p).card)
    (hhalf : 6 * t ≤ (largeRemaining N p).card) :
    2 ^ t ≤ dag.nodes.length := by
  let S := largeRemaining N p
  let C := deletionFamily dag S (3 * t)
  have hcover : ∀ T ∈ S.powersetCard t, ∃ A ∈ C, T ⊆ A := by
    intro T hT
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨q, hq, _, hqsub, hdisj, hqcard⟩ :=
      force_large_target_deletion hv N p hp hturn hS hd T hTsub
        (by simpa only [hTcard] using hbudget)
    have hlargeSub : largeRemaining N q ⊆ S := largeRemaining_mono N hqsub
    have heq : S \ q.remaining = S \ largeRemaining N q := by
      ext x
      simp only [S, largeRemaining, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hsize : (S \ q.remaining).card ≤ 3 * t := by
      rw [heq, Finset.card_sdiff_of_subset hlargeSub]
      rw [hTcard] at hqcard
      dsimp [S]
      omega
    refine ⟨S \ q.remaining, mem_deletionFamily dag S (3 * t) q hq hsize, ?_⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hTsub hx, fun hxq => Finset.disjoint_left.mp hdisj hx hxq⟩
  have hsize : ∀ A ∈ C, A.card ≤ 3 * t := fun _ hA => (Finset.mem_filter.mp hA).2
  have h := target_cover_exponential S C t (3 * t) (by omega) (by dsimp [S]; omega)
    hcover hsize
  exact h.trans (deletionFamily_card_le dag S (3 * t))

/-- The interval root contains exactly the large half of the counters. -/
theorem initial_large_card (N : ℕ) :
    (largeRemaining N (initialPosition N)).card = N - N / 2 := by
  have heq : largeRemaining N (initialPosition N) = largeCounters N := by
    apply Finset.inter_eq_left.mpr
    intro x hx
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  rw [heq, largeCounters, Nat.card_Icc]
  omega

/-- Every full explicit certificate from the actual interval root has exponentially many
nodes. This is conditional on certificate validity and does not prove Catch-Up. -/
theorem initial_certificate_exponential (N t : ℕ) (player : Player)
    (dag : StrategyDAG) (hcert : InitialCertificate N player dag)
    (hN : 16 ≤ N) (ht : 12 * t + 2 ≤ N) :
    2 ^ t ≤ dag.nodes.length := by
  obtain ⟨hv, _, _, hroot⟩ := hcert
  have hp : ContainsPosition dag (initialPosition N) := by
    rw [← hroot]
    exact contains_position_of_contains_state dag dag.root hv.1
  have hS : (initialPosition N).remaining ⊆ Finset.Icc 1 N := Finset.Subset.refl _
  have hd : (initialPosition N).deficit ≤ N := Nat.zero_le _
  have hcard := initial_large_card N
  have hnt := nonterminal_of_two_large N (initialPosition N) hd (by omega)
  cases hplayer : dag.player with
  | p2 =>
      exact large_opponent_node_lower_bound hv N t _ hp
        (by simp [initialPosition, hplayer]) hS hd (by omega) (by omega)
  | p1 =>
      obtain ⟨x, hx, hchild⟩ := owner_step hv _ hp hnt (by simp [initialPosition, hplayer])
      have hb := bounded_after_pick N _ hS hd x hx
      have hc := large_count_after_pick N (initialPosition N) x
      exact large_opponent_node_lower_bound hv N t _ hchild
        (by rw [initial_after_pick]; simp [hplayer]) hb.1 hb.2 (by omega) (by omega)

/-- A convenient explicit exponent, with no auxiliary free parameter. -/
theorem initial_certificate_exponential_floor (N : ℕ) (player : Player)
    (dag : StrategyDAG) (hcert : InitialCertificate N player dag) (hN : 16 ≤ N) :
    2 ^ ((N - 2) / 12) ≤ dag.nodes.length :=
  initial_certificate_exponential N ((N - 2) / 12) player dag hcert hN (by omega)

/-- The exponential lower bound applies to the minimum whenever that minimum is defined. -/
theorem minimumNodes_exponential (N : ℕ) (player : Player)
    (h : CertificateExists N player) (hN : 16 ≤ N) :
    2 ^ ((N - 2) / 12) ≤ minimumNodes N player h := by
  obtain ⟨dag, hdag, hcount⟩ := minimumNodes_realized N player h
  rw [← hcount]
  exact initial_certificate_exponential_floor N player dag hdag hN

end CatchUpSearch.CertificateComplexity
