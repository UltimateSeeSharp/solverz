module

public import CatchUp.Blocks
public import CatchUp.Endgames

/-!
# Tied one-hole blocks in the rounds regime

C108: the rounds game on `{0..2k} \ {o}` at a tie, with `k ≤ o ≤ 2k` and `o ≡ k (mod 2)`, is a draw.
The tied mover's guarantee comes from C23's class `KZc` at the start; the other player's from one
round in which it answers `2k`, or `2k - 1` (`2k - 2` when that is the hole) after the opening
`2k`, after which the state is in `KYc` or `KZc`. The parity of the total forces the margin `0`,
and C13 carries it to the real game above the rounds threshold (`one_hole_block_draw_high`, C105
there). The hole at the top (`o = 2k`) is `roundsValue_range_draw`. Proved here for `k ≥ 3`; at
`k = 2` the sets are two adjacent pairs, a draw at every height by C11 (`one_hole_block_draw_two`).
-/

@[expose] public section

namespace CatchUp

/-- `range n` has no holes, so depth `0`. -/
theorem depth_range (n : ℕ) : depth (Finset.range n) = 0 :=
  depth_eq_zero_of_holes (holes_range n)

/-- Removing one number `o` from `range n` costs at most its distance below the top. -/
theorem depth_range_erase_le {n o : ℕ} (ho : o < n) :
    depth ((Finset.range n).erase o) ≤ n - 1 - o := by
  have hne : (Finset.range n).Nonempty := ⟨o, Finset.mem_range.mpr ho⟩
  have h := depth_erase_le hne (Finset.mem_range.mpr ho)
  have hmax : (Finset.range n).max' hne ≤ n - 1 :=
    Finset.max'_le _ _ _ fun y hy => by rw [Finset.mem_range] at hy; omega
  rw [depth_range] at h
  omega

/-- A set with at least four numbers is in `KZc` once the debt plus `D_Z` fits half its size. -/
theorem kzc_of_four {T : Finset ℕ} {d : ℕ} (h4 : 4 ≤ T.card) (hd : d + depthZ T ≤ T.card / 2) :
    KZc T d :=
  ⟨fun h => by omega, fun _ _ h => by omega, fun _ => hd⟩

/-- A set with at least four numbers is in `KYc` once its depth fits the lead plus half its size
and the lead is positive. -/
theorem kyc_of_four {T : Finset ℕ} {e : ℕ} (h4 : 4 ≤ T.card) (hd : depth T ≤ e + T.card / 2)
    (he : 1 ≤ e) : KYc T e :=
  ⟨fun _ _ h => by omega, fun _ => ⟨hd, fun _ => he⟩⟩

/-- `{0..2k} \ {o}`. -/
abbrev oneHole (k o : ℕ) : Finset ℕ := (Finset.range (2 * k + 1)).erase o

theorem card_oneHole {k o : ℕ} (ho : o ≤ 2 * k) : (oneHole k o).card = 2 * k := by
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
  omega

theorem sum_oneHole {k o : ℕ} (ho : o ≤ 2 * k) : ∑ x ∈ oneHole k o, x + o = k * (2 * k + 1) := by
  rw [Finset.sum_erase_add _ _ (Finset.mem_range.mpr (by omega))]
  have h := Finset.sum_range_id_mul_two (2 * k + 1)
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
  rw [h]
  simp only [Nat.add_sub_cancel]
  ring

/-- **C108 in the rounds game** for `k ≥ 3` and a hole `o` with `k ≤ o < 2k`: the minimax margin at
a tie is `0`. -/
theorem roundsMargin_oneHole {k o : ℕ} (hk : 3 ≤ k) (hlo : k ≤ o) (hhi : o < 2 * k) :
    -1 ≤ roundsMargin (oneHole k o) 0 ∧ roundsMargin (oneHole k o) 0 ≤ 1 := by
  have hc := card_oneHole (k := k) (o := o) (by omega)
  have hev : Even (oneHole k o).card := by rw [hc]; exact even_two_mul k
  have hmem : ∀ {x}, x ∈ oneHole k o ↔ x < 2 * k + 1 ∧ x ≠ o := by
    intro x
    simp only [Finset.mem_erase, Finset.mem_range]
    tauto
  obtain ⟨hZ, -⟩ := depth_class_roundsMargin (2 * k) _ hc (even_two_mul k)
  refine ⟨hZ 0 (kzc_of_four (by omega) ?_), ?_⟩
  · -- Z moves first: `D_Z ≤ depth ≤ 2k - o ≤ k`.
    have h1 := depthZ_le (oneHole k o)
    have h2 : depth (oneHole k o) ≤ 2 * k + 1 - 1 - o := depth_range_erase_le (by omega)
    rw [hc]
    omega
  -- The other player moves first: one round, then C23's classes.
  have hne : (oneHole k o).Nonempty := ⟨2 * k, hmem.mpr ⟨by omega, by omega⟩⟩
  have key := roundsMargin_le_neg hev hne 0 (-1) ?_
  · linarith
  intro i hi
  have hi' := hmem.mp hi
  by_cases hiM : i = 2 * k
  · -- The opening `2k`: answer `2k - 1`, or `2k - 2` when `2k - 1` is the hole.
    subst hiM
    by_cases ho1 : o = 2 * k - 1
    · refine ⟨2 * k - 2, Finset.mem_erase.mpr ⟨by omega, hmem.mpr ⟨by omega, by omega⟩⟩, ?_⟩
      rw [ite_eq_right (show ¬(2 * k ≤ 0 + (2 * k - 2)) by omega)]
      have hT : ((oneHole k o).erase (2 * k)).erase (2 * k - 2) = Finset.range (2 * k - 2) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_range]
        omega
      rw [hT]
      have hc' : (Finset.range (2 * k - 2)).card = 2 * k - 2 := Finset.card_range _
      have hev' : Even (2 * k - 2) := ⟨k - 1, by omega⟩
      obtain ⟨hZ', -⟩ := depth_class_roundsMargin (2 * k - 2) _ hc' hev'
      refine hZ' _ (kzc_of_four (by omega) ?_)
      have h1 := depthZ_le (Finset.range (2 * k - 2))
      rw [depth_range] at h1
      rw [hc']
      omega
    · refine ⟨2 * k - 1, Finset.mem_erase.mpr ⟨by omega, hmem.mpr ⟨by omega, by omega⟩⟩, ?_⟩
      rw [ite_eq_right (show ¬(2 * k ≤ 0 + (2 * k - 1)) by omega)]
      have hT : ((oneHole k o).erase (2 * k)).erase (2 * k - 1) =
          (Finset.range (2 * k - 1)).erase o := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_range]
        omega
      rw [hT]
      have hc' : ((Finset.range (2 * k - 1)).erase o).card = 2 * k - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
        omega
      have hev' : Even (2 * k - 2) := ⟨k - 1, by omega⟩
      obtain ⟨hZ', -⟩ := depth_class_roundsMargin (2 * k - 2) _ hc' hev'
      refine hZ' _ (kzc_of_four (by omega) ?_)
      have h1 := depthZ_le ((Finset.range (2 * k - 1)).erase o)
      have h2 := depth_range_erase_le (n := 2 * k - 1) (o := o) (by omega)
      rw [hc']
      omega
  · -- Any other opening `i`: answer `2k`; Z then leads by `2k - i ≥ 1`.
    refine ⟨2 * k, Finset.mem_erase.mpr ⟨by omega, hmem.mpr ⟨by omega, by omega⟩⟩, ?_⟩
    rw [ite_eq_left (show i ≤ 0 + 2 * k by omega)]
    have hT : ((oneHole k o).erase i).erase (2 * k) = ((Finset.range (2 * k)).erase o).erase i := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_range]
      omega
    rw [hT]
    have hiU : i ∈ (Finset.range (2 * k)).erase o :=
      Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    have hc' : (((Finset.range (2 * k)).erase o).erase i).card = 2 * k - 2 := by
      rw [Finset.card_erase_of_mem hiU, Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),
        Finset.card_range]
      omega
    have hev' : Even (2 * k - 2) := ⟨k - 1, by omega⟩
    obtain ⟨-, hY'⟩ := depth_class_roundsMargin (2 * k - 2) _ hc' hev'
    have hUne : ((Finset.range (2 * k)).erase o).Nonempty := ⟨i, hiU⟩
    have hUmax : ((Finset.range (2 * k)).erase o).max' hUne ≤ 2 * k - 1 :=
      Finset.max'_le _ _ _ fun y hy => by
        rw [Finset.mem_erase, Finset.mem_range] at hy
        omega
    have h1 := depth_erase_le hUne hiU
    have h2 := depth_range_erase_le (n := 2 * k) (o := o) (by omega)
    have := hY' (0 + 2 * k - i) (kyc_of_four (by omega) (by rw [hc']; omega) (by omega))
    linarith

/-- The hole at the top leaves the block `{0..2k-1}`. -/
theorem oneHole_top (k : ℕ) : oneHole k (2 * k) = Finset.range (2 * k) := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_range]
  omega

/-- **C108** for `k ≥ 3`: the rounds game on `{0..2k} \ {o}`, `k ≤ o ≤ 2k`, `o ≡ k (mod 2)`, at a
tie is a draw. -/
theorem roundsValue_oneHole_draw {k o : ℕ} (hk : 3 ≤ k) (hlo : k ≤ o) (hhi : o ≤ 2 * k)
    (hpar : o % 2 = k % 2) : roundsValue (oneHole k o) 0 = .draw := by
  by_cases htop : o = 2 * k
  · subst htop
    rw [oneHole_top]
    have h := roundsValue_range_draw (p := k) (by omega)
    rwa [show k % 2 = 0 by omega] at h
  have hc := card_oneHole (k := k) (o := o) (by omega)
  obtain ⟨h1, h2⟩ := roundsMargin_oneHole hk hlo (by omega)
  have hpar' := even_roundsMargin_add (2 * k) _ hc (even_two_mul k) 0
  rw [← Nat.cast_sum, Int.even_iff] at hpar'
  have hS := sum_oneHole (k := k) (o := o) (by omega)
  have hS2 : (∑ x ∈ oneHole k o, x) % 2 = 0 := by
    have : (k * (2 * k + 1)) % 2 = k % 2 := by
      rw [Nat.mul_mod]
      have : (2 * k + 1) % 2 = 1 := by omega
      rw [this, mul_one, Nat.mod_mod]
    omega
  rw [roundsValue_eq_ofMargin (2 * k) _ hc (even_two_mul k)]
  generalize ∑ x ∈ oneHole k o, x = S at hpar' hS2
  generalize roundsMargin (oneHole k o) 0 = M at hpar' h1 h2 ⊢
  have h0 : M = 0 := by omega
  rw [h0]
  simp [Outcome.ofMargin]

/-- **C105 above the rounds threshold** (C108 with C13), `k ≥ 3`: the odd block
`{a, …, a + 2k}` without `a + o`, `k ≤ o ≤ 2k`, `o ≡ k (mod 2)`, is a draw at a tie once
`a + o > k(2k + 1)`. -/
theorem one_hole_block_draw_high {k o a : ℕ} (hk : 3 ≤ k) (hlo : k ≤ o) (hhi : o ≤ 2 * k)
    (hpar : o % 2 = k % 2) (ha : k * (2 * k + 1) < a + o) (s : ℕ) :
    valueAux ((oneHole k o).map (addLeftEmbedding a)) s s false = .draw := by
  have hc := card_oneHole (k := k) (o := o) hhi
  have hev : Even (oneHole k o).card := by rw [hc]; exact even_two_mul k
  have hS := sum_oneHole (k := k) (o := o) hhi
  have h := valueAux_map_add _ hev a 0 (by omega) s
  rw [Nat.add_zero] at h
  rw [h]
  exact roundsValue_oneHole_draw hk hlo hhi hpar

/-- **C105 at k = 2, every height** (C11): `{a, …, a + 4}` without `a + o`, `o ∈ {0, 2, 4}`, is two
adjacent pairs, a draw at a tie for every `a ≥ 1`. -/
theorem one_hole_block_draw_two {o a : ℕ} (ha : 1 ≤ a) (ho : o ≤ 4) (hpar : o % 2 = 0) (s : ℕ) :
    valueAux ((oneHole 2 o).map (addLeftEmbedding a)) s s false = .draw := by
  have hcases : o = 0 ∨ o = 2 ∨ o = 4 := by omega
  rcases hcases with rfl | rfl | rfl
  · have hT : (oneHole 2 0).map (addLeftEmbedding a) = {a + 1, a + 1 + 1, a + 3, a + 3 + 1} := by
      ext x
      simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_range, addLeftEmbedding_apply,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨y, ⟨hy0, hy⟩, rfl⟩
        omega
      · intro hx
        exact ⟨x - a, ⟨by omega, by omega⟩, by omega⟩
    rw [hT]
    exact valueAux_two_pairs (by omega) (by omega) s
  · have hT : (oneHole 2 2).map (addLeftEmbedding a) = {a, a + 1, a + 3, a + 3 + 1} := by
      ext x
      simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_range, addLeftEmbedding_apply,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨y, ⟨hy0, hy⟩, rfl⟩
        omega
      · intro hx
        exact ⟨x - a, ⟨by omega, by omega⟩, by omega⟩
    rw [hT]
    exact valueAux_two_pairs ha (by omega) s
  · have hT : (oneHole 2 4).map (addLeftEmbedding a) = {a, a + 1, a + 2, a + 2 + 1} := by
      ext x
      simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_range, addLeftEmbedding_apply,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨y, ⟨hy0, hy⟩, rfl⟩
        omega
      · intro hx
        exact ⟨x - a, ⟨by omega, by omega⟩, by omega⟩
    rw [hT]
    exact valueAux_two_pairs ha (by omega) s

end CatchUp
