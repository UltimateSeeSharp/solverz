/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/Earlier/CertificateComplexityGame.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.Earlier.CertificateComplexity
public import CatchUp.CompletedTurn

/-!
# Bounded deletion cost in full Catch-Up certificates

These lemmas use the actual player, terminal condition, and equality switch.
They support target-set covering lower bounds without counting histories as states.
-/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace CatchUpSearch.CertificateComplexity

open CatchUp CertificateChecker

/-- Distinct positive counters have at least the triangular-number sum. -/
theorem card_mul_succ_le_twice_sum (S : Finset ℕ) (hpos : ∀ x ∈ S, 0 < x) :
    S.card * (S.card + 1) ≤ 2 * S.sum (fun x => x) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | @insert a S hmax ih =>
      have ha : 0 < a := hpos a (Finset.mem_insert_self _ _)
      have hposS : ∀ x ∈ S, 0 < x := fun x hx => hpos x (Finset.mem_insert_of_mem hx)
      have hnot : a ∉ S := fun haS => (hmax a haS).false
      have hsub : S ⊆ Finset.Icc 1 (a - 1) := by
        intro x hx
        exact Finset.mem_Icc.mpr ⟨hposS x hx, by have := hmax x hx; omega⟩
      have hcard := Finset.card_le_card hsub
      rw [Nat.card_Icc] at hcard
      have hi := ih hposS
      rw [Finset.card_insert_of_notMem hnot, Finset.sum_insert hnot]
      have : S.card + 1 ≤ a := by omega
      nlinarith

/-- A reachable normalized deficit never exceeds the interval's largest counter. -/
theorem bounded_after_pick (N : ℕ) (p : GamePosition)
    (hS : p.remaining ⊆ Finset.Icc 1 N) (hd : p.deficit ≤ N)
    (x : ℕ) (hx : p.LegalMove x) :
    (p.afterPick x).remaining ⊆ Finset.Icc 1 N ∧ (p.afterPick x).deficit ≤ N := by
  have hxb := Finset.mem_Icc.mp (hS hx)
  constructor
  · exact (Finset.erase_subset x p.remaining).trans hS
  · simp only [GamePosition.afterPick, Position.afterPick]
    split_ifs <;> omega

/-- The interval bound persists along an actual pick trace. -/
theorem bounded_after_trace (N : ℕ) {p q : GamePosition} {xs : List ℕ}
    (trace : GamePosition.PickTrace p xs q)
    (hS : p.remaining ⊆ Finset.Icc 1 N) (hd : p.deficit ≤ N) :
    q.remaining ⊆ Finset.Icc 1 N ∧ q.deficit ≤ N := by
  induction trace with
  | nil => exact ⟨hS, hd⟩
  | @cons p x xs q step tail ih =>
      have hx : p.LegalMove x := by
        rcases step.2 with ⟨y, hy, heq⟩
        have hrem := congrArg (fun q : GamePosition => q.remaining) heq
        by_contra hnot
        have he : p.remaining.erase x = p.remaining := Finset.erase_eq_of_notMem hnot
        simp only [GamePosition.afterPick, Position.afterPick] at hrem
        have : y ∈ p.remaining.erase y := by rw [← hrem, he]; exact hy
        exact Finset.notMem_erase y p.remaining this
      have h := bounded_after_pick N p hS hd x hx
      exact ih h.1 h.2

/-- Many remaining distinct positive counters exclude both terminal conditions. -/
theorem nonterminal_of_half_remaining (N : ℕ) (hN : 16 ≤ N) (p : GamePosition)
    (hS : p.remaining ⊆ Finset.Icc 1 N) (hd : p.deficit ≤ N)
    (hcard : N / 2 ≤ p.remaining.card) : ¬p.IsTerminal := by
  have hs := card_mul_succ_le_twice_sum p.remaining
    (fun x hx => (Finset.mem_Icc.mp (hS hx)).1)
  have hc : 8 ≤ p.remaining.card := by omega
  have hn : N ≤ 2 * p.remaining.card + 1 := by omega
  have hsum : N < p.remaining.sum (fun x => x) := by nlinarith
  intro ht
  rcases ht with he | hl
  · simp [he] at hc
  · omega

/-- The number of picks in any completed turn is bounded by a triangular threshold. -/
theorem completed_turn_length_le (N h : ℕ) (hh : 1 ≤ h)
    (hthreshold : 2 * N ≤ h * (h + 1))
    {p q : GamePosition} {xs : List ℕ} (trace : CompletedTurn p xs q)
    (hpos : ∀ x ∈ p.remaining, 0 < x) (hd : p.deficit ≤ N) : xs.length ≤ h := by
  have hex : ∃ pre last, xs = pre ++ [last] := by
    cases xs using List.reverseRecOn with
    | nil => exact False.elim (trace.picks_nonempty rfl)
    | append_singleton pre last => exact ⟨pre, last, rfl⟩
  obtain ⟨pre, last, rfl⟩ := hex
  have hnodup : pre.Nodup := (List.nodup_append.mp trace.picks_nodup).1
  have hposPre : ∀ x ∈ pre.toFinset, 0 < x := by
    intro x hx
    apply hpos x
    apply trace.picks_subset_remaining
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hx))
  have hs := card_mul_succ_le_twice_sum pre.toFinset hposPre
  rw [List.toFinset_card_of_nodup hnodup, List.sum_toFinset _ hnodup] at hs
  have hsum : (List.map (fun x : ℕ => x) pre).sum = pre.sum := by simp
  rw [hsum] at hs
  rcases trace.preparation_sum_lt_or_empty with hempty | hlt
  · simp [hempty, hh]
  · have hlen : pre.length < h := by
      by_contra hn
      have hhpre : h ≤ pre.length := by omega
      have hprod : h * (h + 1) ≤ pre.length * (pre.length + 1) :=
        Nat.mul_le_mul hhpre (by omega)
      nlinarith
    simpa using hlen

/-- Deleting a completed turn reduces remaining cardinality by exactly its length. -/
theorem completed_turn_card (p q : GamePosition) (xs : List ℕ)
    (trace : CompletedTurn p xs q) :
    p.remaining.card = q.remaining.card + xs.length := by
  have hsub : xs.toFinset ⊆ p.remaining := trace.picks_subset_remaining
  rw [trace.after_remaining, Finset.card_sdiff_of_subset hsub,
    List.toFinset_card_of_nodup trace.picks_nodup]
  have hle := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup trace.picks_nodup] at hle
  omega

/-- Valid owner nodes expose their selected, covered child. -/
theorem owner_step {dag : StrategyDAG} (hv : DAGValid dag)
    (p : GamePosition) (hp : ContainsPosition dag p)
    (hnt : ¬p.IsTerminal) (hturn : p.toMove = dag.player) :
    ∃ x, p.LegalMove x ∧ ContainsPosition dag (p.afterPick x) := by
  obtain ⟨node, hnode, rfl⟩ := List.mem_map.mp hp
  have hn := node_valid_of_dag_valid hv hnode
  cases hb : node.branch with
  | terminal =>
      simp only [NodeValid, hb] at hn
      exact False.elim (hnt hn.2.1)
  | owner x =>
      simp only [NodeValid, hb] at hn
      exact ⟨x, hn.2.2.2.1, hn.2.2.2.2.1⟩
  | opponent xs =>
      simp only [NodeValid, hb] at hn
      exact False.elim (hn.2.2.1 hturn)

/-- Valid opponent nodes cover every legal child, not merely optimal moves. -/
theorem opponent_step {dag : StrategyDAG} (hv : DAGValid dag)
    (p : GamePosition) (hp : ContainsPosition dag p)
    (hnt : ¬p.IsTerminal) (hturn : p.toMove ≠ dag.player)
    (x : ℕ) (hx : p.LegalMove x) : ContainsPosition dag (p.afterPick x) := by
  obtain ⟨node, hnode, rfl⟩ := List.mem_map.mp hp
  have hn := node_valid_of_dag_valid hv hnode
  cases hb : node.branch with
  | terminal =>
      simp only [NodeValid, hb] at hn
      exact False.elim (hnt hn.2.1)
  | owner y =>
      simp only [NodeValid, hb] at hn
      exact False.elim (hturn hn.2.2.1)
  | opponent xs =>
      simp only [NodeValid, hb] at hn
      have hxlist : x ∈ xs := by
        rw [hn.2.2.2.1]
        exact (mem_available_counters_iff_legal_move _ _ _).mpr hx
      exact ((List.forall_iff_forall_mem.mp hn.2.2.2.2) x hxlist).2.1

/-- Following the certificate's protected choices reaches a completed-turn endpoint in it. -/
theorem owner_completed_turn {dag : StrategyDAG} (hv : DAGValid dag)
    (p : GamePosition) (hp : ContainsPosition dag p)
    (hnt : ¬p.IsTerminal) (hturn : p.toMove = dag.player) :
    ∃ xs q, CompletedTurn p xs q ∧ ContainsPosition dag q := by
  obtain ⟨x, hx, hchild⟩ := owner_step hv p hp hnt hturn
  by_cases hbehind : x < p.deficit
  · have hchildnt := p.after_pick_not_terminal_of_lt x hnt hx hbehind
    have hchildturn : (p.afterPick x).toMove = dag.player := by
      rw [GamePosition.to_move_after_pick_of_lt _ _ hbehind, hturn]
    obtain ⟨xs, q, htrace, hq⟩ :=
      owner_completed_turn hv (p.afterPick x) hchild hchildnt hchildturn
    exact ⟨x :: xs, q, CompletedTurn.more p x xs q hx hbehind htrace, hq⟩
  · exact ⟨[x], p.afterPick x, CompletedTurn.finish p x hx (by omega), hchild⟩
termination_by p.remaining.card
decreasing_by exact GamePosition.remaining_card_after_pick_lt _ _ hx

/-- One adversarial target pick, followed by the certificate's protected turn if necessary,
deletes at most `h + 1` counters and returns to an adversarial node. -/
theorem adversary_macro {dag : StrategyDAG} (hv : DAGValid dag)
    (N h : ℕ) (hN : 16 ≤ N) (hh : 1 ≤ h) (hthreshold : 2 * N ≤ h * (h + 1))
    (p : GamePosition) (hp : ContainsPosition dag p) (hturn : p.toMove ≠ dag.player)
    (hS : p.remaining ⊆ Finset.Icc 1 N) (hd : p.deficit ≤ N)
    (hcard : N / 2 + (h + 1) ≤ p.remaining.card)
    (x : ℕ) (hx : p.LegalMove x) :
    ∃ q, ContainsPosition dag q ∧ q.toMove ≠ dag.player ∧
      q.remaining ⊆ p.remaining ∧ x ∉ q.remaining ∧
      p.remaining.card ≤ q.remaining.card + (h + 1) ∧
      q.remaining ⊆ Finset.Icc 1 N ∧ q.deficit ≤ N := by
  have hnt := nonterminal_of_half_remaining N hN p hS hd (by omega)
  have hchild := opponent_step hv p hp hnt hturn x hx
  have hb := bounded_after_pick N p hS hd x hx
  have hc : (p.afterPick x).remaining.card + 1 = p.remaining.card :=
    Finset.card_erase_add_one hx
  have hchildSub : (p.afterPick x).remaining ⊆ p.remaining := Finset.erase_subset _ _
  have hxnot : x ∉ (p.afterPick x).remaining := Finset.notMem_erase _ _
  by_cases hbehind : x < p.deficit
  · refine ⟨p.afterPick x, hchild, ?_, hchildSub, hxnot, ?_, hb⟩
    · simpa only [GamePosition.to_move_after_pick_of_lt _ _ hbehind] using hturn
    · omega
  · have hchildTurn : (p.afterPick x).toMove = dag.player := by
      rw [GamePosition.to_move_after_pick_of_le _ _ (by omega)]
      exact (Player.other_eq_iff_ne _ _).mpr hturn
    have hchildNt := nonterminal_of_half_remaining N hN (p.afterPick x) hb.1 hb.2
      (by omega)
    obtain ⟨xs, q, trace, hq⟩ := owner_completed_turn hv _ hchild hchildNt hchildTurn
    have hlen := completed_turn_length_le N h hh hthreshold trace
      (fun y hy => (Finset.mem_Icc.mp (hb.1 hy)).1) hb.2
    have hcount := completed_turn_card _ _ _ trace
    have hqSub : q.remaining ⊆ (p.afterPick x).remaining := by
      rw [trace.after_remaining]
      exact Finset.sdiff_subset
    have hqb := bounded_after_trace N trace.pick_trace hb.1 hb.2
    refine ⟨q, hq, ?_, hqSub.trans hchildSub, fun hxq => hxnot (hqSub hxq), ?_, hqb⟩
    · rw [trace.after_to_move, hchildTurn]
      cases dag.player <;> decide
    · omega

/-- A certificate must allow deletion of every chosen target set at bounded cardinality cost. -/
theorem force_target_deletion {dag : StrategyDAG} (hv : DAGValid dag)
    (N h : ℕ) (hN : 16 ≤ N) (hh : 1 ≤ h) (hthreshold : 2 * N ≤ h * (h + 1))
    (p : GamePosition) (hp : ContainsPosition dag p) (hturn : p.toMove ≠ dag.player)
    (hS : p.remaining ⊆ Finset.Icc 1 N) (hd : p.deficit ≤ N)
    (T : Finset ℕ) (hT : T ⊆ p.remaining)
    (hcard : N / 2 + (h + 1) * T.card ≤ p.remaining.card) :
    ∃ q, ContainsPosition dag q ∧ q.toMove ≠ dag.player ∧ q.remaining ⊆ p.remaining ∧
      Disjoint T q.remaining ∧ p.remaining.card ≤ q.remaining.card + (h + 1) * T.card := by
  by_cases he : T = ∅
  · subst T
    exact ⟨p, hp, hturn, Finset.Subset.refl _, by simp, by simp⟩
  · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have htpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨x, hx⟩
    have hM : h + 1 ≤ (h + 1) * T.card := by nlinarith
    obtain ⟨q, hq, hqturn, hqsub, hxnot, hqcard, hqS, hqd⟩ :=
      adversary_macro hv N h hN hh hthreshold p hp hturn hS hd (by omega) x (hT hx)
    let U := T ∩ q.remaining
    have hUsub : U ⊆ T.erase x := by
      intro y hy
      have hy' := Finset.mem_inter.mp hy
      exact Finset.mem_erase.mpr ⟨by intro heq; subst y; exact hxnot hy'.2, hy'.1⟩
    have hUcard : U.card < T.card :=
      (Finset.card_le_card hUsub).trans_lt (Finset.card_erase_lt_of_mem hx)
    have hUq : U ⊆ q.remaining := Finset.inter_subset_right
    have hbudget : N / 2 + (h + 1) * U.card ≤ q.remaining.card := by
      have hmul : (h + 1) * (U.card + 1) ≤ (h + 1) * T.card :=
        Nat.mul_le_mul_left _ hUcard
      nlinarith
    obtain ⟨r, hr, hrturn, hrsub, hrdisj, hrcard⟩ :=
      force_target_deletion hv N h hN hh hthreshold q hq hqturn hqS hqd U hUq hbudget
    refine ⟨r, hr, hrturn, hrsub.trans hqsub, ?_, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro y hyT hyr
      exact Finset.disjoint_left.mp hrdisj (Finset.mem_inter.mpr ⟨hyT, hrsub hyr⟩) hyr
    · have hmul : (h + 1) * (U.card + 1) ≤ (h + 1) * T.card :=
        Nat.mul_le_mul_left _ hUcard
      nlinarith
termination_by T.card

decreasing_by exact hUcard

/-- Deleted-set projections of listed nodes, restricted to a cardinality budget. -/
def deletionFamily (dag : StrategyDAG) (S : Finset ℕ) (a : ℕ) : Finset (Finset ℕ) :=
  ((dag.nodes.map (fun node => S \ (toGamePosition dag.gameSize node.state).remaining)).toFinset).filter
    (fun A => A.card ≤ a)

/-- Projection and filtering cannot increase the number of listed nodes. -/
theorem deletionFamily_card_le (dag : StrategyDAG) (S : Finset ℕ) (a : ℕ) :
    (deletionFamily dag S a).card ≤ dag.nodes.length := by
  apply (Finset.card_filter_le _ _).trans
  simpa only [List.length_map] using List.toFinset_card_le
    (dag.nodes.map fun node => S \ (toGamePosition dag.gameSize node.state).remaining)

/-- A contained position supplies its deleted-set projection when it fits the budget. -/
theorem mem_deletionFamily (dag : StrategyDAG) (S : Finset ℕ) (a : ℕ)
    (q : GamePosition) (hq : ContainsPosition dag q) (hsize : (S \ q.remaining).card ≤ a) :
    S \ q.remaining ∈ deletionFamily dag S a := by
  refine Finset.mem_filter.mpr ⟨?_, hsize⟩
  obtain ⟨node, hnode, heq⟩ := List.mem_map.mp hq
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨node, hnode, by rw [heq]⟩

/-- Target covering forces exponentially many full DAG nodes from a sufficiently large
adversary position. -/
theorem opponent_node_lower_bound {dag : StrategyDAG} (hv : DAGValid dag)
    (N h t : ℕ) (hN : 16 ≤ N) (hh : 1 ≤ h) (hthreshold : 2 * N ≤ h * (h + 1))
    (p : GamePosition) (hp : ContainsPosition dag p) (hturn : p.toMove ≠ dag.player)
    (hS : p.remaining ⊆ Finset.Icc 1 N) (hd : p.deficit ≤ N)
    (hbudget : N / 2 + (h + 1) * t ≤ p.remaining.card)
    (hhalf : 2 * ((h + 1) * t) ≤ p.remaining.card) :
    2 ^ t ≤ dag.nodes.length := by
  let a := (h + 1) * t
  let C := deletionFamily dag p.remaining a
  have hcover : ∀ T ∈ p.remaining.powersetCard t, ∃ A ∈ C, T ⊆ A := by
    intro T hT
    obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨q, hq, _, hqsub, hdisj, hqcard⟩ :=
      force_target_deletion hv N h hN hh hthreshold p hp hturn hS hd T hTsub
        (by simpa only [hTcard] using hbudget)
    have hsize : (p.remaining \ q.remaining).card ≤ a := by
      rw [Finset.card_sdiff_of_subset hqsub]
      dsimp [a]
      rw [hTcard] at hqcard
      omega
    refine ⟨p.remaining \ q.remaining, mem_deletionFamily dag _ a q hq hsize, ?_⟩
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hTsub hx, fun hxq => Finset.disjoint_left.mp hdisj hx hxq⟩
  have hsize : ∀ A ∈ C, A.card ≤ a := fun _ hA => (Finset.mem_filter.mp hA).2
  have hta : t ≤ a := by dsimp [a]; nlinarith
  exact (target_cover_exponential p.remaining C t a hta hhalf hcover hsize).trans
    (deletionFamily_card_le dag p.remaining a)

/-- A conditional explicit-DAG lower bound for either player, starting at the actual
interval root. It does not assert the existence of any certificate. -/
theorem initial_certificate_node_lower_bound (N h t : ℕ) (player : Player)
    (dag : StrategyDAG) (hcert : InitialCertificate N player dag)
    (hN : 16 ≤ N) (hh : 1 ≤ h) (hthreshold : 2 * N ≤ h * (h + 1))
    (ht : 2 * ((h + 1) * t) ≤ N - 1) :
    2 ^ t ≤ dag.nodes.length := by
  obtain ⟨hv, _, _, hroot⟩ := hcert
  have hp : ContainsPosition dag (initialPosition N) := by
    rw [← hroot]
    exact contains_position_of_contains_state dag dag.root hv.1
  have hS : (initialPosition N).remaining ⊆ Finset.Icc 1 N := Finset.Subset.refl _
  have hd : (initialPosition N).deficit ≤ N := Nat.zero_le _
  have hcard : (initialPosition N).remaining.card = N := by simp [initialPosition]
  have hnt := nonterminal_of_half_remaining N hN _ hS hd (by rw [hcard]; omega)
  cases hplayer : dag.player with
  | p2 =>
      exact opponent_node_lower_bound hv N h t hN hh hthreshold _ hp
        (by simp [initialPosition, hplayer]) hS hd
        (by rw [hcard]; omega) (by rw [hcard]; omega)
  | p1 =>
      obtain ⟨x, hx, hchild⟩ := owner_step hv _ hp hnt (by simp [initialPosition, hplayer])
      have hb := bounded_after_pick N _ hS hd x hx
      have hc : ((initialPosition N).afterPick x).remaining.card + 1 = N := by
        simpa only [hcard, GamePosition.afterPick, Position.afterPick] using Finset.card_erase_add_one hx
      exact opponent_node_lower_bound hv N h t hN hh hthreshold _ hchild
        (by rw [initial_after_pick]; simp [hplayer]) hb.1 hb.2
        (by omega) (by omega)

end CatchUpSearch.CertificateComplexity
