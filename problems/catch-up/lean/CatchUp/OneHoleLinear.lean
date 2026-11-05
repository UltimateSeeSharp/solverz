module

public import CatchUp.Linear
public import CatchUp.OneHoleRounds

/-!
# Tied one-hole blocks at linear height

C108 at linear height: the odd block `{a..a + 2k}` without `a + o`, `k ≤ o ≤ 2k`, `o ≡ k (mod 2)`,
is a draw at a tie once `a > 3(2k + 1)`, against `a + o > k(2k + 1)` in `one_hole_block_draw_high`.
The strategy is `Linear.lean`'s (AM+T, then matching partners after the switch) on blocks of
`2(k + 1)` offsets, which contain the one-hole set; the tied opponent's first round is
`OneHoleRounds.lean`'s (answer `2k`, or `2k - 1` / `2k - 2` after the opening `2k`). C22
(`valueAux_transfer`) carries both guarantees to the real game. The same classes give part of C110's
band, `1 ≤ d ≤ o + 1 - k` (`one_hole_band_draw_linear`).
-/

@[expose] public section

namespace CatchUp

/-- The opponent's round starts: `Linear.lean`'s, plus the tied one-hole start. -/
def HY1 (k o : ℕ) (T : Finset ℕ) (e : ℕ) : Prop :=
  HY (k + 1) T e ∨ (T = oneHole k o ∧ e = 0)

theorem mem_oneHole {k o x : ℕ} : x ∈ oneHole k o ↔ x < 2 * k + 1 ∧ x ≠ o := by
  simp only [Finset.mem_erase, Finset.mem_range]
  tauto

theorem sum_oneHole_mod_two {k o : ℕ} (ho : o ≤ 2 * k) (hpar : o % 2 = k % 2) :
    (∑ x ∈ oneHole k o, x) % 2 = 0 := by
  have hS := sum_oneHole (k := k) (o := o) ho
  have : (k * (2 * k + 1)) % 2 = k % 2 := by
    rw [Nat.mul_mod]
    have : (2 * k + 1) % 2 = 1 := by omega
    rw [this, mul_one, Nat.mod_mod]
  omega

theorem oneHole_subset_range {k o : ℕ} : oneHole k o ⊆ Finset.range (2 * (k + 1)) :=
  fun x hx => Finset.mem_range.mpr (by have := (mem_oneHole.mp hx).1; omega)

/-- Taking two numbers from a set: the sum drops by them and the rest is a subset. -/
theorem sum_erase_two {T : Finset ℕ} {i j : ℕ} (hi : i ∈ T) (hj : j ∈ T.erase i) :
    ∑ x ∈ (T.erase i).erase j, x + j + i = ∑ x ∈ T, x ∧ (T.erase i).erase j ⊆ T := by
  have hs1 := Finset.sum_erase_add T (fun x => x) hi
  have hs2 := Finset.sum_erase_add (T.erase i) (fun x => x) hj
  exact ⟨by omega, fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)⟩

/-- The tied opponent's first round (C108's): every opening `i` has an answer leading into
`Linear.lean`'s classes. -/
theorem hy1_start {k o : ℕ} (hk : 3 ≤ k) (hlo : k ≤ o) (hhi : o < 2 * k)
    (hpar : o % 2 = k % 2) :
    ∀ i ∈ oneHole k o, ∃ j ∈ (oneHole k o).erase i,
      (i ≤ 0 + j → HY1 k o (((oneHole k o).erase i).erase j) (0 + j - i)) ∧
      (¬ i ≤ 0 + j → HZ (k + 1) (((oneHole k o).erase i).erase j) (i - 0 - j)) := by
  intro i hi
  have hi' := mem_oneHole.mp hi
  have hS := sum_oneHole_mod_two (k := k) (o := o) (by omega) hpar
  by_cases hiM : i = 2 * k
  · subst hiM
    by_cases ho1 : o = 2 * k - 1
    · -- Answer `2k - 2`: Z trails by 2 on `{0..2k-3}`.
      have hj : 2 * k - 2 ∈ (oneHole k o).erase (2 * k) :=
        Finset.mem_erase.mpr ⟨by omega, mem_oneHole.mpr ⟨by omega, by omega⟩⟩
      refine ⟨2 * k - 2, hj, fun h => absurd h (by omega), fun _ => ?_⟩
      obtain ⟨hs, hsub⟩ := sum_erase_two hi hj
      have hT : ((oneHole k o).erase (2 * k)).erase (2 * k - 2) = Finset.range (2 * k - 2) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_range]
        omega
      rw [hT] at hs hsub ⊢
      have hc' : (Finset.range (2 * k - 2)).card = 2 * k - 2 := Finset.card_range _
      refine ⟨hsub.trans oneHole_subset_range, ⟨k - 1, by rw [hc']; omega⟩, by omega,
        kzc_of_four (by omega) ?_, by omega⟩
      have h1 := depthZ_le (Finset.range (2 * k - 2))
      rw [depth_range] at h1
      rw [hc']
      omega
    · -- Answer `2k - 1`: Z trails by 1 on `{0..2k-2} \ {o}`.
      have hj : 2 * k - 1 ∈ (oneHole k o).erase (2 * k) :=
        Finset.mem_erase.mpr ⟨by omega, mem_oneHole.mpr ⟨by omega, by omega⟩⟩
      refine ⟨2 * k - 1, hj, fun h => absurd h (by omega), fun _ => ?_⟩
      obtain ⟨hs, hsub⟩ := sum_erase_two hi hj
      have hT : ((oneHole k o).erase (2 * k)).erase (2 * k - 1) =
          (Finset.range (2 * k - 1)).erase o := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_range]
        omega
      rw [hT] at hs hsub ⊢
      have hc' : ((Finset.range (2 * k - 1)).erase o).card = 2 * k - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
        omega
      refine ⟨hsub.trans oneHole_subset_range, ⟨k - 1, by rw [hc']; omega⟩, by omega,
        kzc_of_four (by omega) ?_, by omega⟩
      have h1 := depthZ_le ((Finset.range (2 * k - 1)).erase o)
      have h2 := depth_range_erase_le (n := 2 * k - 1) (o := o) (by omega)
      rw [hc']
      omega
  · -- Any other opening `i`: answer `2k`; Z then leads by `2k - i ≥ 1`.
    have hj : 2 * k ∈ (oneHole k o).erase i :=
      Finset.mem_erase.mpr ⟨by omega, mem_oneHole.mpr ⟨by omega, by omega⟩⟩
    refine ⟨2 * k, hj, fun _ => Or.inl ?_, fun h => absurd (by omega) h⟩
    obtain ⟨hs, hsub⟩ := sum_erase_two hi hj
    have hT : ((oneHole k o).erase i).erase (2 * k) =
        ((Finset.range (2 * k)).erase o).erase i := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
    rw [hT] at hs hsub ⊢
    have hiU : i ∈ (Finset.range (2 * k)).erase o :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    have hc' : (((Finset.range (2 * k)).erase o).erase i).card = 2 * k - 2 := by
      rw [Finset.card_erase_of_mem hiU, Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),
        Finset.card_range]
      omega
    have hUne : ((Finset.range (2 * k)).erase o).Nonempty := ⟨i, hiU⟩
    have hUmax : ((Finset.range (2 * k)).erase o).max' hUne ≤ 2 * k - 1 :=
      Finset.max'_le _ _ _ fun y hy => by
        rw [Finset.mem_erase, Finset.mem_range] at hy
        omega
    have h1 := depth_erase_le hUne hiU
    have h2 := depth_range_erase_le (n := 2 * k) (o := o) (by omega)
    have hKY := kyc_of_four (T := ((Finset.range (2 * k)).erase o).erase i) (e := 0 + 2 * k - i)
      (by omega) (by rw [hc']; omega) (by omega)
    have hsubR := hsub.trans oneHole_subset_range
    have hcost := matchCost_le_range (p := k + 1) (by omega) hsubR
    refine ⟨hsubR, ⟨k - 1, by rw [hc']; omega⟩, by omega, ?_⟩
    by_cases hle : ((0 + 2 * k - i : ℕ) : ℤ) ≤ matchCost (((Finset.range (2 * k)).erase o).erase i)
    · exact Or.inl ⟨hle, hKY, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩

/-- **C108 at linear height** (C105 there), `k ≥ 3`: the odd block `{a, …, a + 2k}` without
`a + o`, `k ≤ o ≤ 2k`, `o ≡ k (mod 2)`, is a draw at a tie once `a > 3(2k + 1)`. -/
theorem one_hole_block_draw_linear {k o a : ℕ} (hk : 3 ≤ k) (hlo : k ≤ o) (hhi : o ≤ 2 * k)
    (hpar : o % 2 = k % 2) (ha : 3 * (2 * (k + 1) - 1) < a) (s : ℕ) :
    valueAux ((oneHole k o).map (addLeftEmbedding a)) s s false = .draw := by
  by_cases htop : o = 2 * k
  · subst htop
    rw [oneHole_top]
    have h := block_row_draw_linear (p := k) (a := a) (d := 0) (by omega) (by omega) (by omega)
      (by omega) s
    simpa using h
  have hT := valueAux_transfer a (HZ (k + 1)) (HY1 k o)
    (fun T d hK o' ho' => by
      have := Finset.mem_range.mp (hK.1 ho'); have := hK.2.2.2.2; omega)
    (fun T e hK o' ho' => by
      rcases hK with hK | ⟨rfl, rfl⟩
      · have := Finset.mem_range.mp (hK.1 ho')
        rcases hK.2.2.2 with ⟨-, -, he⟩ | ⟨-, he⟩
        · omega
        · have := matchCost_nonneg _ T rfl; omega
      · have := (mem_oneHole.mp ho').1; omega)
    (fun d hK => by
      have h1 := hK.2.2.2.1.1 (by simp)
      have h2 := hK.2.2.1
      simp at h2
      omega)
    (fun T d hK h => ⟨T.max' h, Finset.max'_mem T h, fun j hj =>
      ⟨(hz_step hK h j hj).1, fun hc => Or.inl ((hz_step hK h j hj).2 hc)⟩⟩)
    (fun T e hK => by
      rcases hK with hK | ⟨rfl, rfl⟩
      · intro i hi
        obtain ⟨j, hj, h1, h2⟩ := hy_step hK i hi
        exact ⟨j, hj, fun hc => Or.inl (h1 hc), h2⟩
      · exact hy1_start hk hlo (by omega) hpar)
    (2 * k) (oneHole k o) (card_oneHole (by omega))
  have hc := card_oneHole (k := k) (o := o) hhi
  have hZ0 : KZc (oneHole k o) 0 := by
    refine kzc_of_four (by omega) ?_
    have h1 := depthZ_le (oneHole k o)
    have h2 : depth (oneHole k o) ≤ 2 * k + 1 - 1 - o := depth_range_erase_le (by omega)
    rw [hc]
    omega
  have hZ := hT.1 0 ⟨oneHole_subset_range, ⟨k, by omega⟩,
    by have := sum_oneHole_mod_two hhi hpar; omega, hZ0, by omega⟩ s
  have hY := hT.2 0 (Or.inr ⟨rfl, rfl⟩) s
  rw [Nat.add_zero] at hZ hY
  revert hZ hY
  cases valueAux ((oneHole k o).map (addLeftEmbedding a)) s s false <;> simp

/-- `D_Z` of a one-hole block: the hole's distance below `2k - 1`. -/
theorem depthZ_oneHole_le {k o : ℕ} (ho : o < 2 * k) :
    depthZ (oneHole k o) ≤ 2 * k - 1 - o := by
  have hne : (oneHole k o).Nonempty := ⟨2 * k, mem_oneHole.mpr ⟨by omega, by omega⟩⟩
  have hmax : (oneHole k o).max' hne = 2 * k :=
    le_antisymm (Finset.max'_le _ _ _ fun y hy => by have := (mem_oneHole.mp hy).1; omega)
      (Finset.le_max' _ _ (mem_oneHole.mpr ⟨by omega, by omega⟩))
  rw [depthZ_of_nonempty hne, hmax]
  have hT : (oneHole k o).erase (2 * k) = (Finset.range (2 * k)).erase o := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_range]
    omega
  rw [hT]
  exact depth_range_erase_le (by omega)

/-- **Part of C110's band at linear height**, `k ≥ 3`: the odd block `{a, …, a + 2k}` without
`a + o`, `k ≤ o ≤ 2k`, is a draw for the mover trailing by `d` with `1 ≤ d ≤ o + 1 - k`
(`d ≤ k` when `o = 2k`) of the draw parity, once `a > 3(2k + 1)`. -/
theorem one_hole_band_draw_linear {k o a d : ℕ} (hk : 3 ≤ k) (hlo : k ≤ o) (hhi : o ≤ 2 * k)
    (hd1 : 1 ≤ d) (hd : d + (2 * k - 1 - o) ≤ k) (hdk : d ≤ k)
    (hpar : (d + ∑ x ∈ oneHole k o, x) % 2 = 0) (ha : 3 * (2 * (k + 1) - 1) < a) (s : ℕ) :
    valueAux ((oneHole k o).map (addLeftEmbedding a)) s (s + d) false = .draw := by
  have hT := valueAux_transfer a (HZ (k + 1)) (HY (k + 1))
    (fun T d hK o' ho' => by
      have := Finset.mem_range.mp (hK.1 ho'); have := hK.2.2.2.2; omega)
    (fun T e hK o' ho' => by
      have := Finset.mem_range.mp (hK.1 ho')
      rcases hK.2.2.2 with ⟨-, -, he⟩ | ⟨-, he⟩
      · omega
      · have := matchCost_nonneg _ T rfl; omega)
    (fun d hK => by
      have h1 := hK.2.2.2.1.1 (by simp)
      have h2 := hK.2.2.1
      simp at h2
      omega)
    (fun T d hK h => ⟨T.max' h, Finset.max'_mem T h, hz_step hK h⟩)
    (fun T e hK => hy_step hK)
    (2 * k) (oneHole k o) (card_oneHole hhi)
  have hc := card_oneHole (k := k) (o := o) hhi
  have hev : Even (oneHole k o).card := ⟨k, by omega⟩
  have hZd : KZc (oneHole k o) d := by
    refine kzc_of_four (by omega) ?_
    rw [hc]
    by_cases htop : o = 2 * k
    · subst htop
      rw [oneHole_top]
      have h1 := depthZ_le (Finset.range (2 * k))
      rw [depth_range] at h1
      omega
    · have := depthZ_oneHole_le (k := k) (o := o) (by omega)
      omega
  have hYd : KYc (oneHole k o) d := by
    refine kyc_of_four (by omega) ?_ hd1
    have h2 : depth (oneHole k o) ≤ 2 * k + 1 - 1 - o := depth_range_erase_le (by omega)
    rw [hc]
    omega
  have hcost :=
    matchCost_le_range (p := k + 1) (by omega) (oneHole_subset_range (k := k) (o := o))
  have hY : HY (k + 1) (oneHole k o) d := by
    refine ⟨oneHole_subset_range, hev, hpar, ?_⟩
    by_cases hle : (d : ℤ) ≤ matchCost (oneHole k o)
    · exact Or.inl ⟨hle, hYd, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
  have hZ := hT.1 d ⟨oneHole_subset_range, hev, hpar, hZd, by omega⟩ s
  have hY := hT.2 d hY s
  revert hZ hY
  cases valueAux ((oneHole k o).map (addLeftEmbedding a)) s (s + d) false <;> simp

end CatchUp
