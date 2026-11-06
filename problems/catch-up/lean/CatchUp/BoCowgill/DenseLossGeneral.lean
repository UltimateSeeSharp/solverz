/-
Copyright 2026 The Catch-Up Research Authors.
Licensed under the Apache License, Version 2.0; see https://www.apache.org/licenses/LICENSE-2.0.
From catch-up-research (b0853b4), CatchUp/DenseLossGeneral.lean.
Modified for solverz: ported to Lean/Mathlib v4.35.0; module system (imports all of Mathlib, as
theirs did).
-/
module

public import Mathlib
public import CatchUp.BoCowgill.ExactSumLossObstruction

/-! # Dense losing positions and an exact-deficit boundary corollary -/

-- Vendored: kept in catch-up-research's style, so style linters are off.
set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

@[expose] public section

open Finset
namespace CatchUp.DenseLossGeneral

open CatchUp (Position.loss_after_continuing_pick)

/-- A missing counter above twice the hole budget leaves an intact small complement pair. -/
theorem exists_small_complement_pair
    (N h d : ℕ) (S : Finset ℕ) (_hS : S ⊆ Icc 1 N)
    (hholes : (Icc 1 N \ S).card ≤ h) (hlarge : 2 * h + 1 ≤ d)
    (hdN : d ≤ N) (hdS : d ∉ S) :
    ∃ i, 1 ≤ i ∧ i ≤ h ∧ i ∈ S ∧ d - i ∈ S := by
  classical
  by_contra hex
  let holes := Icc 1 N \ S
  let f : ℕ → ℕ := fun i ↦ if i ∈ S then d - i else i
  have hnot (i : ℕ) (hi : i ∈ Icc 1 h) (hiS : i ∈ S) : d - i ∉ S := by
    intro hc
    exact hex ⟨i, (mem_Icc.mp hi).1, (mem_Icc.mp hi).2, hiS, hc⟩
  have hdholes : d ∈ holes := by
    apply mem_sdiff.mpr
    exact ⟨mem_Icc.mpr ⟨by omega, hdN⟩, hdS⟩
  have hmap : Set.MapsTo f (Icc 1 h) (holes.erase d) := by
    intro i hi
    change i ∈ Finset.Icc 1 h at hi
    change f i ∈ holes.erase d
    have hib := mem_Icc.mp hi
    by_cases hiS : i ∈ S
    · simp only [f, ite_eq_left hiS]
      apply mem_erase.mpr
      refine ⟨by omega, ?_⟩
      apply mem_sdiff.mpr
      exact ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hnot i hi hiS⟩
    · simp only [f, ite_eq_right hiS]
      apply mem_erase.mpr
      refine ⟨by omega, ?_⟩
      apply mem_sdiff.mpr
      exact ⟨mem_Icc.mpr ⟨hib.1, by omega⟩, hiS⟩
  have hinj : Set.InjOn f (Icc 1 h) := by
    intro i hi j hj he
    change i ∈ Finset.Icc 1 h at hi
    change j ∈ Finset.Icc 1 h at hj
    have hib := mem_Icc.mp hi
    have hjb := mem_Icc.mp hj
    dsimp [f] at he
    split_ifs at he <;> omega
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  have hdom : (Icc 1 h).card = h := by simp
  rw [hdom] at hc
  have he := Finset.card_erase_add_one hdholes
  change holes.card ≤ h at hholes
  omega

/-- A dense loss either descends above the old deficit after at most three deletions,
or descends through a missing counter below the hole budget. -/
theorem loss_dichotomy
    (N h d : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 N)
    (hholes : (Icc 1 N \ S).card ≤ h) (hlarge : 2 * h + 1 ≤ d) (hdN : d ≤ N)
    (hloss : (⟨S, d⟩ : Position).value = .loss) :
    (∃ B : Finset ℕ, B.Nonempty ∧ B ⊆ S ∧ B.card ≤ 2 ∧
      B.sum (fun x ↦ x) = d ∧ ∃ w ∈ S \ B,
        d < w ∧ (afterOpening (S \ B) w).value = .loss) ∨
    (∃ t, 1 ≤ t ∧ t < h ∧ t ∉ S ∧ d - t ∈ S ∧
      (⟨S.erase (d - t), t⟩ : Position).value = .loss) := by
  classical
  by_cases hdS : d ∈ S
  · left
    have hb : ({d} : Finset ℕ).Nonempty := by simp
    obtain ⟨w, hw, hwin, hgt⟩ :=
      Position.exists_winning_opening_gt_max_of_loss_of_exact_sum S {d} d hb
        (by intro x hx; simp only [mem_singleton] at hx; subst x; omega)
        (by simpa using hdS) (by simp) hloss
    refine ⟨{d}, hb, by simpa using hdS, by simp, by simp, w, hw, ?_, hwin⟩
    simpa using hgt
  · have hex := exists_small_complement_pair N h d S hS hholes hlarge hdN hdS
    let i := Nat.find hex
    have hi : 1 ≤ i ∧ i ≤ h ∧ i ∈ S ∧ d - i ∈ S := Nat.find_spec hex
    have hid : i < d - i := by omega
    have hb : ({i, d - i} : Finset ℕ).Nonempty := by simp
    have hsub : ({i, d - i} : Finset ℕ) ⊆ S := by
      intro y hy
      simp only [mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hi.2.2.1
      · exact hi.2.2.2
    have hsum : ({i, d - i} : Finset ℕ).sum (fun y ↦ y) = d := by
      simp [ne_of_lt hid]
      omega
    obtain ⟨w, hw, hwin, hgt⟩ :=
      Position.exists_winning_opening_gt_max_of_loss_of_exact_sum S {i, d - i} d hb
        (by intro y hy; have hp := hS (hsub hy); exact (mem_Icc.mp hp).1)
        hsub hsum hloss
    have hwi : d - i < w :=
      lt_of_le_of_lt (Finset.le_max' {i, d - i} (d - i) (by simp)) hgt
    by_cases hdw : d < w
    · exact Or.inl ⟨{i, d - i}, hb, hsub, by simp [ne_of_lt hid], hsum,
        w, hw, hdw, hwin⟩
    · right
      have hwS : w ∈ S := (mem_sdiff.mp hw).1
      have hwd : w < d := by
        have hne : w ≠ d := by intro he; subst w; exact hdS hwS
        omega
      have htpos : 1 ≤ d - w := by omega
      have hti : d - w < i := by omega
      have hwback : d - (d - w) = w := by omega
      have htmissing : d - w ∉ S := by
        intro htS
        have hpair : 1 ≤ d - w ∧ d - w ≤ h ∧ d - w ∈ S ∧ d - (d - w) ∈ S :=
          ⟨htpos, by omega, htS, by simpa only [hwback] using hwS⟩
        have hmin : i ≤ d - w := Nat.find_min' hex hpair
        omega
      have hcatch : ¬ S.sum (fun y ↦ y) < d := by
        have hle := Finset.sum_le_sum_of_subset (f := fun y : ℕ ↦ y) hsub
        rw [hsum] at hle
        omega
      have hl := Position.loss_after_continuing_pick (⟨S, d⟩ : Position)
        hwS hcatch hwd hloss
      refine ⟨d - w, htpos, by omega, htmissing, ?_, ?_⟩
      · simpa only [hwback] using hwS
      · simpa [Position.afterPick, hwd, hwback] using hl

/-- Representability of every positive sum below the hole budget suffices at exact deficit. -/
theorem exact_deficit_nonloss_of_low_subsums
    (h d : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ h) (hlarge : 2 * h + 1 ≤ d)
    (hrep : ∀ t, 1 ≤ t → t < h → ∃ A : Finset ℕ,
      A ⊆ S ∧ A.sum (fun x ↦ x) = t) : (⟨S, d⟩ : Position).value ≠ .loss := by
  classical
  have hne : S.Nonempty := by
    by_cases hdS : d ∈ S
    · exact ⟨d, hdS⟩
    · obtain ⟨i, _, _, hiS, _⟩ :=
        exists_small_complement_pair d h d S hS hholes hlarge le_rfl hdS
      exact ⟨i, hiS⟩
  let M := S.max' hne
  have hMmem : M ∈ S := Finset.max'_mem S hne
  have hMd : M ≤ d := (mem_Icc.mp (hS hMmem)).2
  have hMmax (x : ℕ) (hx : x ∈ S) : x ≤ M := Finset.le_max' S x hx
  let k := d - M
  have hU : Icc (M + 1) d ⊆ Icc 1 d \ S := by
    intro x hx
    have hp := mem_Icc.mp hx
    refine mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, hp.2⟩, ?_⟩
    intro hxS
    have hm := hMmax x hxS
    omega
  have hUcard : (Icc (M + 1) d).card = k := by
    rw [Nat.card_Icc]
    dsimp [k]
    omega
  have hk : k ≤ h := by
    have hc := Finset.card_le_card hU
    rw [hUcard] at hc
    omega
  have hMk : k < M := by dsimp [k] at *; omega
  have hA : ∃ A : Finset ℕ, A ⊆ S ∧ A.sum (fun x ↦ x) = k := by
    by_cases hk0 : k = 0
    · exact ⟨∅, by simp, by simp [hk0]⟩
    · by_cases hkh : k < h
      · exact hrep k (by omega) hkh
      · have hkeq : k = h := by omega
        have hkS : k ∈ S := by
          by_contra hknot
          have hsub : insert k (Icc (M + 1) d) ⊆ Icc 1 d \ S := by
            intro x hx
            rcases mem_insert.mp hx with rfl | hx
            · exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by dsimp [k]; omega⟩, hknot⟩
            · exact hU hx
          have hkU : k ∉ Icc (M + 1) d := by simp only [mem_Icc]; omega
          have hc := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hkU, hUcard] at hc
          omega
        exact ⟨{k}, by simpa using hkS, by simp⟩
  obtain ⟨A, hAS, hsumA⟩ := hA
  have hMA : M ∉ A := by
    intro hmem
    have hm := Finset.single_le_sum (fun x _ ↦ Nat.zero_le x) hmem
    change M ≤ A.sum (fun x ↦ x) at hm
    omega
  have hB : (insert M A).Nonempty := ⟨M, by simp⟩
  have hBS : insert M A ⊆ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hMmem
    · exact hAS hx
  apply Position.value_ne_loss_of_exact_sum_block_dominates S (insert M A) d hB
    (by intro x hx; exact (mem_Icc.mp (hS (hBS hx))).1) hBS
  · rw [Finset.sum_insert hMA, hsumA]
    dsimp [k]
    omega
  · intro x hx
    exact le_trans (hMmax x (mem_sdiff.mp hx).1)
      (Finset.le_max' (insert M A) M (by simp))

/-- At exact deficit d, the low prefix and at most h holes rule out loss uniformly in d. -/
theorem exact_deficit_nonloss
    (h d : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc 1 d)
    (hholes : (Icc 1 d \ S).card ≤ h) (hlarge : 2 * h + 1 ≤ d)
    (hprefix : Icc 1 (h - 1) ⊆ S) : (⟨S, d⟩ : Position).value ≠ .loss := by
  apply exact_deficit_nonloss_of_low_subsums h d S hS hholes hlarge
  intro t htpos hth
  refine ⟨{t}, ?_, by simp⟩
  simpa using hprefix (mem_Icc.mpr ⟨htpos, by omega⟩)

/-- The maximum counter is not a strictly winning original opening once N is at least three. -/
theorem after_max_opening_nonloss (N : ℕ) (hN : 3 ≤ N) :
    (afterOpening (Icc 1 N) N).value ≠ .loss := by
  change (⟨(Icc 1 N).erase N, N⟩ : Position).value ≠ .loss
  apply exact_deficit_nonloss 1 N _ (Finset.erase_subset _ _)
  · have hsub : Icc 1 N \ (Icc 1 N).erase N ⊆ {N} := by
      intro y hy
      simp only [mem_sdiff, mem_erase, mem_singleton] at hy ⊢
      tauto
    have hc := Finset.card_le_card hsub
    simpa using hc
  · omega
  · simp

end CatchUp.DenseLossGeneral
