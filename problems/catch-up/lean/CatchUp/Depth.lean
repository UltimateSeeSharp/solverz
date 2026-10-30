module

public import CatchUp.Potential
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The depth invariant

Claim C23. Holes of a set are the numbers strictly between its least and greatest element that
it lacks; `depth T` sums their distances below the top (`D_Y`), `depthZ T` the same without the top
(`D_Z`). The classes `KZc` (Z moves, trailing by `d`: `d + D_Z ≤ q`) and `KYc` (the opponent moves,
trailing by `e`: `D_Y ≤ e + q`, and `e ≥ 1` if there are holes), with explicit last rounds, are
closed under every round where Z plays AM+T (`closeZ`, `closeY`), so Z's minimax margin is at least
`-1` from them (`depth_class_roundsMargin`). Intervals have no holes (`kzc_range`, `kyc_range`).
-/

@[expose] public section

namespace CatchUp

/-- Holes of `T`: numbers strictly between its least and greatest element that are not in it. -/
noncomputable def holes (T : Finset ℕ) : Finset ℕ :=
  if h : T.Nonempty then (Finset.Ioo (T.min' h) (T.max' h)).filter (· ∉ T) else ∅

/-- Total depth of the holes below the greatest element (`D_Y` of C23). -/
noncomputable def depth (T : Finset ℕ) : ℕ :=
  if h : T.Nonempty then ∑ x ∈ holes T, (T.max' h - x) else 0

theorem mem_holes {T : Finset ℕ} (h : T.Nonempty) {x : ℕ} :
    x ∈ holes T ↔ T.min' h < x ∧ x < T.max' h ∧ x ∉ T := by
  simp [holes, h, Finset.mem_Ioo, and_assoc]

theorem depth_of_nonempty {T : Finset ℕ} (h : T.Nonempty) :
    depth T = ∑ x ∈ holes T, (T.max' h - x) := by
  simp [depth, h]

theorem holes_empty : holes ∅ = ∅ := by simp [holes]

/-- Removing the greatest element keeps the least one when two or more are left. -/
theorem min'_erase_max' {U : Finset ℕ} (h : U.Nonempty) (h' : (U.erase (U.max' h)).Nonempty) :
    (U.erase (U.max' h)).min' h' = U.min' h := by
  apply le_antisymm
  · apply Finset.min'_le
    refine Finset.mem_erase.mpr ⟨?_, Finset.min'_mem U h⟩
    intro he
    obtain ⟨y, hy⟩ := h'
    have h1 := Finset.min'_le U y (Finset.mem_of_mem_erase hy)
    have h2 := Finset.le_max' U y (Finset.mem_of_mem_erase hy)
    exact (Finset.mem_erase.mp hy).1 (by omega)
  · exact Finset.le_min' _ _ _ fun y hy => Finset.min'_le U y (Finset.mem_of_mem_erase hy)

theorem max'_erase_lt {U : Finset ℕ} (h : U.Nonempty) (h' : (U.erase (U.max' h)).Nonempty) :
    (U.erase (U.max' h)).max' h' < U.max' h := by
  apply lt_of_le_of_ne
  · exact Finset.max'_le _ _ _ fun y hy => Finset.le_max' U y (Finset.mem_of_mem_erase hy)
  · exact fun he => (Finset.notMem_erase _ U) (he ▸ Finset.max'_mem _ h')

/-- Removing the greatest element: every hole is at depth ≥ 1, and the remaining holes lose at
least 1 of depth, so `depth (U \ max) + #holes U ≤ depth U`. -/
theorem depth_erase_max' {U : Finset ℕ} (h : U.Nonempty) :
    depth (U.erase (U.max' h)) + (holes U).card ≤ depth U := by
  by_cases h' : (U.erase (U.max' h)).Nonempty
  · have hsub : holes (U.erase (U.max' h)) ⊆ holes U := by
      intro x hx
      rw [mem_holes h'] at hx
      rw [mem_holes h]
      obtain ⟨h1, h2, h3⟩ := hx
      rw [min'_erase_max' h h'] at h1
      have h4 := max'_erase_lt h h'
      refine ⟨h1, by omega, fun hx => h3 (Finset.mem_erase.mpr ⟨by omega, hx⟩)⟩
    rw [depth_of_nonempty h', depth_of_nonempty h]
    have hlt := max'_erase_lt h h'
    calc ∑ x ∈ holes (U.erase (U.max' h)), ((U.erase (U.max' h)).max' h' - x) + (holes U).card
        ≤ ∑ x ∈ holes (U.erase (U.max' h)), (U.max' h - x - 1) + ∑ x ∈ holes U, 1 := by
          rw [Finset.card_eq_sum_ones]
          apply Nat.add_le_add_right
          apply Finset.sum_le_sum
          intro x _
          omega
      _ ≤ ∑ x ∈ holes U, (U.max' h - x - 1) + ∑ x ∈ holes U, 1 := by
          gcongr
      _ = ∑ x ∈ holes U, (U.max' h - x) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x hx
          rw [mem_holes h] at hx
          omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp h']
    have hU : holes U = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      rw [mem_holes h]
      rintro ⟨h1, h2, -⟩
      exact h' ⟨U.min' h, Finset.mem_erase.mpr ⟨by omega, Finset.min'_mem U h⟩⟩
    rw [hU]
    simp [depth]

/-- Removing a number strictly inside makes it a hole. -/
theorem depth_erase_inner {U : Finset ℕ} (h : U.Nonempty) {x : ℕ} (hx : x ∈ U)
    (hlo : U.min' h < x) (hhi : x < U.max' h) :
    depth (U.erase x) = depth U + (U.max' h - x) := by
  have h' : (U.erase x).Nonempty := ⟨U.max' h, Finset.mem_erase.mpr ⟨by omega, Finset.max'_mem U h⟩⟩
  have hmax : (U.erase x).max' h' = U.max' h := max'_erase_of_ne h (by omega) h'
  have hmin : (U.erase x).min' h' = U.min' h := by
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨by omega, Finset.min'_mem U h⟩)
    · exact Finset.le_min' _ _ _ fun y hy => Finset.min'_le U y (Finset.mem_of_mem_erase hy)
  have hset : holes (U.erase x) = insert x (holes U) := by
    ext y
    rw [mem_holes h', Finset.mem_insert, mem_holes h, hmax, hmin]
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hy : y = x
      · exact Or.inl hy
      · exact Or.inr ⟨h1, h2, fun hy' => h3 ⟨hy, hy'⟩⟩
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨hlo, hhi, fun h => h.1 rfl⟩
      · exact ⟨h1, h2, fun h => h3 h.2⟩
  have hxn : x ∉ holes U := fun hm => ((mem_holes h).mp hm).2.2 hx
  rw [depth_of_nonempty h', depth_of_nonempty h, hset, Finset.sum_insert hxn, hmax]
  ring

/-- Removing the least number removes holes. -/
theorem depth_erase_min' {U : Finset ℕ} (h : U.Nonempty) (h2 : 2 ≤ U.card) :
    depth (U.erase (U.min' h)) ≤ depth U := by
  have h' : (U.erase (U.min' h)).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.card_erase_add_one (Finset.min'_mem U h)
    omega
  have hmax : (U.erase (U.min' h)).max' h' = U.max' h := by
    apply max'_erase_of_ne h _ h'
    intro he
    obtain ⟨y, hy⟩ := h'
    have h1 := Finset.min'_le U y (Finset.mem_of_mem_erase hy)
    have h3 := Finset.le_max' U y (Finset.mem_of_mem_erase hy)
    exact (Finset.mem_erase.mp hy).1 (by omega)
  have hmin : U.min' h ≤ (U.erase (U.min' h)).min' h' :=
    Finset.le_min' _ _ _ fun y hy => Finset.min'_le U y (Finset.mem_of_mem_erase hy)
  rw [depth_of_nonempty h', depth_of_nonempty h, hmax]
  apply Finset.sum_le_sum_of_subset
  intro y hy
  rw [mem_holes h'] at hy
  rw [mem_holes h]
  obtain ⟨h1, h2, h3⟩ := hy
  rw [hmax] at h2
  refine ⟨by omega, h2, fun hy' => h3 (Finset.mem_erase.mpr ⟨?_, hy'⟩)⟩
  omega

/-- C23 (B): removing any number costs at most its distance below the top. -/
theorem depth_erase_le {U : Finset ℕ} (h : U.Nonempty) {x : ℕ} (hx : x ∈ U) :
    depth (U.erase x) ≤ depth U + (U.max' h - x) := by
  by_cases hmax : x = U.max' h
  · subst hmax
    have := depth_erase_max' h
    omega
  by_cases hmin : x = U.min' h
  · have h2 : 2 ≤ U.card := by
      have h1 : U.min' h < U.max' h := lt_of_le_of_ne (Finset.min'_le U _ (Finset.max'_mem U h))
        (fun he => hmax (hmin.trans he))
      have : 1 < U.card := Finset.one_lt_card.mpr ⟨_, Finset.min'_mem U h, _, Finset.max'_mem U h,
        ne_of_lt h1⟩
      omega
    subst hmin
    have := depth_erase_min' h h2
    omega
  · have hlo : U.min' h < x := lt_of_le_of_ne (Finset.min'_le U x hx) (Ne.symm hmin)
    have hhi : x < U.max' h := lt_of_le_of_ne (Finset.le_max' U x hx) hmax
    rw [depth_erase_inner h hx hlo hhi]

/-- Sum of the depths `t - x` over the gap strictly between `b` and `t`. -/
noncomputable def gapSum (b t : ℕ) : ℕ := ∑ x ∈ Finset.Ioo b t, (t - x)

/-- A gap of `G = t - b - 1` holes has total depth at least `2G - 1` (the deepest is `G`). -/
theorem gapSum_ge (b t : ℕ) : 2 * (t - b - 1) ≤ gapSum b t + 1 := by
  unfold gapSum
  by_cases hbt : b + 1 < t
  · have hmem : b + 1 ∈ Finset.Ioo b t := Finset.mem_Ioo.mpr ⟨by omega, hbt⟩
    have h1 : ∑ x ∈ Finset.Ioo b t, (t - x) = ∑ x ∈ Finset.Ioo b t, ((t - x - 1) + 1) :=
      Finset.sum_congr rfl fun x hx => by rw [Finset.mem_Ioo] at hx; omega
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul, Nat.cast_id,
      mul_one]
    have h2 : t - (b + 1) - 1 ≤ ∑ x ∈ Finset.Ioo b t, (t - x - 1) :=
      Finset.single_le_sum_of_canonicallyOrdered (f := fun x => t - x - 1) hmem
    omega
  · omega

/-- The holes of `U` are those of `U` without its top, plus the gap below the top. -/
theorem holes_eq_union {U : Finset ℕ} (h : U.Nonempty) (h' : (U.erase (U.max' h)).Nonempty) :
    holes U =
      holes (U.erase (U.max' h)) ∪ Finset.Ioo ((U.erase (U.max' h)).max' h') (U.max' h) := by
  have hmin := min'_erase_max' h h'
  have hlt := max'_erase_lt h h'
  ext x
  rw [Finset.mem_union, mem_holes h, mem_holes h', Finset.mem_Ioo, hmin]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hx : x < (U.erase (U.max' h)).max' h'
    · exact Or.inl ⟨h1, hx, fun hx' => h3 (Finset.mem_of_mem_erase hx')⟩
    · refine Or.inr ⟨?_, h2⟩
      apply lt_of_le_of_ne (not_lt.mp hx)
      intro he
      exact h3 (Finset.mem_of_mem_erase (he ▸ Finset.max'_mem _ h'))
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, by omega, fun hx => h3 (Finset.mem_erase.mpr ⟨by omega, hx⟩)⟩
    · refine ⟨?_, h2, fun hx => ?_⟩
      · have := Finset.min'_le _ _ (Finset.max'_mem _ h')
        rw [hmin] at this
        omega
      · have : x ∈ U.erase (U.max' h) := Finset.mem_erase.mpr ⟨by omega, hx⟩
        have := Finset.le_max' _ x this
        omega

theorem disjoint_holes_gap {U : Finset ℕ} (h : U.Nonempty) (h' : (U.erase (U.max' h)).Nonempty) :
    Disjoint (holes (U.erase (U.max' h)))
      (Finset.Ioo ((U.erase (U.max' h)).max' h') (U.max' h)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_holes h'] at hx
  rw [Finset.mem_Ioo] at hx'
  omega

/-- C23 (C), one step: removing the top `t` with next number `t'`. -/
theorem depth_eq_erase_max' {U : Finset ℕ} (h : U.Nonempty) (h' : (U.erase (U.max' h)).Nonempty) :
    depth U = depth (U.erase (U.max' h)) +
      (holes (U.erase (U.max' h))).card * (U.max' h - (U.erase (U.max' h)).max' h') +
      gapSum ((U.erase (U.max' h)).max' h') (U.max' h) := by
  have hlt := max'_erase_lt h h'
  rw [depth_of_nonempty h, holes_eq_union h h', Finset.sum_union (disjoint_holes_gap h h'),
    depth_of_nonempty h', gapSum, Finset.card_eq_sum_ones, Finset.sum_mul, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [mem_holes h'] at hx
  omega

theorem card_holes_eq {U : Finset ℕ} (h : U.Nonempty) (h' : (U.erase (U.max' h)).Nonempty) :
    (holes U).card = (holes (U.erase (U.max' h))).card +
      (U.max' h - (U.erase (U.max' h)).max' h' - 1) := by
  rw [holes_eq_union h h', Finset.card_union_of_disjoint (disjoint_holes_gap h h'), Nat.card_Ioo]

theorem depth_eq_zero_of_holes {U : Finset ℕ} (hU : holes U = ∅) : depth U = 0 := by
  unfold depth
  split_ifs <;> simp [hU]

theorem holes_of_card_le_one {U : Finset ℕ} (hU : U.card ≤ 1) : holes U = ∅ := by
  by_cases h : U.Nonempty
  · ext x
    simp only [Finset.notMem_empty, iff_false]
    rw [mem_holes h]
    rintro ⟨h1, h2, -⟩
    have := Finset.card_le_one.mp hU _ (Finset.min'_mem U h) _ (Finset.max'_mem U h)
    omega
  · simp [holes, h]

theorem depth_of_card_le_one {U : Finset ℕ} (hU : U.card ≤ 1) : depth U = 0 :=
  depth_eq_zero_of_holes (holes_of_card_le_one hU)

theorem card_erase_max' {U : Finset ℕ} (h : U.Nonempty) :
    (U.erase (U.max' h)).card + 1 = U.card := Finset.card_erase_add_one (Finset.max'_mem U h)

/-- A two-element set's depth is its gap's. -/
theorem depth_two {U : Finset ℕ} (h : U.Nonempty) (h' : (U.erase (U.max' h)).Nonempty)
    (h2 : U.card = 2) : depth U = gapSum ((U.erase (U.max' h)).max' h') (U.max' h) := by
  have hc := card_erase_max' h
  rw [depth_eq_erase_max' h h', depth_of_card_le_one (by omega),
    holes_of_card_le_one (U := U.erase (U.max' h)) (by omega)]
  simp

/-- `D_Z` of C23: the depth of `T` without its top. -/
noncomputable def depthZ (T : Finset ℕ) : ℕ :=
  if h : T.Nonempty then depth (T.erase (T.max' h)) else 0

theorem depthZ_of_nonempty {T : Finset ℕ} (h : T.Nonempty) :
    depthZ T = depth (T.erase (T.max' h)) := by simp [depthZ, h]

theorem depthZ_le (T : Finset ℕ) : depthZ T ≤ depth T := by
  by_cases h : T.Nonempty
  · rw [depthZ_of_nonempty h]
    have := depth_erase_max' h
    omega
  · simp [depthZ, h]

/-- C23's class where Z moves, trailing by `d`. -/
def KZc (T : Finset ℕ) (d : ℕ) : Prop :=
  (T.card = 0 → d ≤ 1) ∧
  (∀ (h : T.Nonempty) (h' : (T.erase (T.max' h)).Nonempty), T.card = 2 →
      d ≤ T.max' h - (T.erase (T.max' h)).max' h' + 1) ∧
  (4 ≤ T.card → d + depthZ T ≤ T.card / 2)

/-- C23's class where the opponent moves, trailing by `e` (Z leads by `e`). -/
def KYc (T : Finset ℕ) (e : ℕ) : Prop :=
  (∀ (h : T.Nonempty) (h' : (T.erase (T.max' h)).Nonempty), T.card = 2 →
      T.max' h - (T.erase (T.max' h)).max' h' ≤ e + 1) ∧
  (4 ≤ T.card → depth T ≤ e + T.card / 2 ∧ ((holes T).Nonempty → 1 ≤ e))

/-- A two-element set whose depth is at most `e + 1`, with `e ≥ 1`, meets `KYc`'s last-round
bound (C23 (D)). -/
theorem kyc_two_of_depth {T : Finset ℕ} {e : ℕ} (h2 : T.card = 2) (he : 1 ≤ e)
    (hd : depth T ≤ e + 1) : KYc T e := by
  refine ⟨fun h h' _ => ?_, fun h4 => by omega⟩
  rw [depth_two h h' h2] at hd
  have := gapSum_ge ((T.erase (T.max' h)).max' h') (T.max' h)
  omega

/-- C23 case (Z): Z takes the top `t₁`, the opponent any `j`. -/
theorem closeZ {T : Finset ℕ} (hev : Even T.card) (h : T.Nonempty) {d : ℕ} (hK : KZc T d)
    {j : ℕ} (hj : j ∈ T.erase (T.max' h)) :
    (T.max' h ≤ d + j → KZc ((T.erase (T.max' h)).erase j) (d + j - T.max' h)) ∧
    (¬ T.max' h ≤ d + j → KYc ((T.erase (T.max' h)).erase j) (T.max' h - d - j)) := by
  have hU : (T.erase (T.max' h)).Nonempty := ⟨j, hj⟩
  have hcU := card_erase_max' h
  have hcT' := Finset.card_erase_add_one hj
  have hjt2 : j ≤ (T.erase (T.max' h)).max' hU := Finset.le_max' _ j hj
  have ht21 := max'_erase_lt h hU
  obtain ⟨k, hk⟩ := hev
  obtain ⟨hK0, hK2, hK4⟩ := hK
  by_cases h2 : T.card = 2
  · -- Last round: nothing is left after it.
    have h0 : (T.erase (T.max' h)).erase j = ∅ := Finset.card_eq_zero.mp (by omega)
    have hjt : j = (T.erase (T.max' h)).max' hU :=
      Finset.card_le_one.mp (by omega) _ hj _ (Finset.max'_mem _ hU)
    have hd := hK2 h hU h2
    rw [h0]
    refine ⟨fun hc => ⟨fun _ => by omega, fun h'' => absurd h'' Finset.not_nonempty_empty,
      fun h4 => by simp at h4⟩, fun _ => ⟨fun h'' => absurd h'' Finset.not_nonempty_empty,
      fun h4 => by simp at h4⟩⟩
  have h4 : 4 ≤ T.card := by omega
  have hq := hK4 h4
  rw [depthZ_of_nonempty h] at hq
  have hB := depth_erase_le hU hj
  have hZ' := depthZ_le ((T.erase (T.max' h)).erase j)
  constructor
  · intro hc
    refine ⟨fun h0 => by omega, fun h' h'' h2' => ?_, fun h4' => ?_⟩
    · omega
    · omega
  · intro hc
    by_cases h2' : ((T.erase (T.max' h)).erase j).card = 2
    · exact kyc_two_of_depth h2' (by omega) (by omega)
    · refine ⟨fun _ _ h2'' => absurd h2'' h2', fun h4' => ⟨by omega, fun _ => by omega⟩⟩

/-- In a two-element set, the larger element is the top and the smaller the next. -/
theorem two_elems {T : Finset ℕ} (h2 : T.card = 2) (h : T.Nonempty)
    (hU : (T.erase (T.max' h)).Nonempty) {x y : ℕ} (hx : x ∈ T) (hy : y ∈ T) (hxy : y < x) :
    T.max' h = x ∧ (T.erase (T.max' h)).max' hU = y := by
  have hmx : T.max' h = x := by
    by_contra hne
    have hle := Finset.le_max' T x hx
    have : 2 < T.card := Finset.two_lt_card.mpr ⟨T.max' h, Finset.max'_mem T h, x, hx, y, hy,
      hne, by omega, by omega⟩
    omega
  refine ⟨hmx, ?_⟩
  have hc := card_erase_max' h
  have hyU : y ∈ T.erase (T.max' h) := Finset.mem_erase.mpr ⟨by omega, hy⟩
  exact Finset.card_le_one.mp (by omega) _ (Finset.max'_mem _ hU) _ hyU

theorem amtReply_of_ne_max {T : Finset ℕ} (h : T.Nonempty) {i : ℕ} (hi : i ∈ T)
    (hit : i ≠ T.max' h) (hUi : (T.erase i).Nonempty) (e : ℕ) :
    amtReply (T.erase i) e i = T.max' h := by
  have hmax : (T.erase i).max' hUi = T.max' h := max'_erase_of_ne h hit hUi
  have hle : i < T.max' h := lt_of_le_of_ne (Finset.le_max' T i hi) hit
  unfold amtReply
  simp only [hUi, ↓reduceDIte, hmax]
  have : ¬ (e + T.max' h = i ∧ ((T.erase i).erase (T.max' h)).Nonempty) := by
    rintro ⟨h1, -⟩; omega
  simp only [this, ↓reduceDIte]

theorem amtReply_top_tie {U : Finset ℕ} (hU : U.Nonempty) {e t : ℕ}
    (hex : e + U.max' hU = t ∧ (U.erase (U.max' hU)).Nonempty) :
    amtReply U e t = (U.erase (U.max' hU)).max' hex.2 := by
  unfold amtReply; simp only [hU, ↓reduceDIte, hex, and_self]

theorem amtReply_top_no_tie {U : Finset ℕ} (hU : U.Nonempty) {e t : ℕ}
    (hex : ¬ (e + U.max' hU = t ∧ (U.erase (U.max' hU)).Nonempty)) :
    amtReply U e t = U.max' hU := by
  unfold amtReply; simp only [hU, ↓reduceDIte, hex]

/-- C23 cases (Y1)–(Y3): the opponent picks `i`, Z answers by AM+T. -/
theorem closeY {T : Finset ℕ} (hev : Even T.card) {e : ℕ} (hK : KYc T e) {i : ℕ} (hi : i ∈ T) :
    (i ≤ e + amtReply (T.erase i) e i →
      KYc ((T.erase i).erase (amtReply (T.erase i) e i)) (e + amtReply (T.erase i) e i - i)) ∧
    (¬ i ≤ e + amtReply (T.erase i) e i →
      KZc ((T.erase i).erase (amtReply (T.erase i) e i)) (i - e - amtReply (T.erase i) e i)) := by
  have h : T.Nonempty := ⟨i, hi⟩
  have hUi := erase_nonempty_of_even hev hi
  have hU := erase_nonempty_of_even hev (Finset.max'_mem T h)
  have hcU := card_erase_max' h
  have hcUi := Finset.card_erase_add_one hi
  obtain ⟨hK2, hK4⟩ := hK
  have ht21 := max'_erase_lt h hU
  have hev' := hev
  obtain ⟨k, hk⟩ := hev
  by_cases h2 : T.card = 2
  · -- Last round: nothing is left after it.
    have hjm := amtReply_mem hUi e i
    have hcj := Finset.card_erase_add_one hjm
    have h0 : (T.erase i).erase (amtReply (T.erase i) e i) = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    rw [h0]
    refine ⟨fun _ => ⟨fun h'' => absurd h'' Finset.not_nonempty_empty, fun h4 => by simp at h4⟩,
      fun hc => ⟨fun _ => ?_, fun h'' => absurd h'' Finset.not_nonempty_empty,
        fun h4 => by simp at h4⟩⟩
    have hjT := Finset.mem_of_mem_erase hjm
    obtain ⟨hm1, hm2⟩ := two_elems h2 h hU hi hjT (by omega)
    have hd := hK2 h hU h2
    rw [hm2, hm1] at hd
    omega
  have h4 : 4 ≤ T.card := by omega
  obtain ⟨hq, hhol⟩ := hK4 h4
  -- Names: t₁ > t₂ > t₃, U = T \ t₁, T'' = U \ t₂.
  have hT'' : ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).Nonempty := by
    rw [← Finset.card_pos]; have := card_erase_max' hU; omega
  have hc'' := card_erase_max' hU
  have ht32 := max'_erase_lt hU hT''
  have hdT := depth_eq_erase_max' h hU
  have hdU := depth_eq_erase_max' hU hT''
  have hcT := card_holes_eq h hU
  have hcU' := card_holes_eq hU hT''
  have hg1 := gapSum_ge ((T.erase (T.max' h)).max' hU) (T.max' h)
  have hg2 := gapSum_ge (((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'')
    ((T.erase (T.max' h)).max' hU)
  have hF5 := depth_erase_max' hT''
  rw [← depthZ_of_nonempty hT''] at hF5
  have hm0 : (holes ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU))).card = 0 →
      depth ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)) = 0 :=
    fun h0 => depth_eq_zero_of_holes (Finset.card_eq_zero.mp h0)
  have hholT : (holes T).card ≥ 1 → 1 ≤ e := fun h1 => hhol (Finset.card_pos.mp (by omega))
  -- Products as atoms with the bounds the cases need.
  set a1 := T.max' h - (T.erase (T.max' h)).max' hU with ha1
  set b1 := (T.erase (T.max' h)).max' hU -
    ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'' with hb1
  set m := (holes ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU))).card with hm
  set hU' := (holes (T.erase (T.max' h))).card with hhU'
  have hX1 : 1 ≤ hU' → a1 ≤ hU' * a1 := fun h1 => Nat.le_mul_of_pos_left a1 h1
  have hX2 : 2 ≤ hU' → 2 * a1 ≤ hU' * a1 := fun h1 => Nat.mul_le_mul_right a1 h1
  have hY1 : 1 ≤ m → b1 ≤ m * b1 := fun h1 => Nat.le_mul_of_pos_left b1 h1
  have hY2 : m ≤ m * b1 := Nat.le_mul_of_pos_right m (by omega)
  have hcd := depthZ_le ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU))
  by_cases hit : i = T.max' h
  · subst hit
    by_cases hex : e + (T.erase (T.max' h)).max' hU = T.max' h ∧
        ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).Nonempty
    · -- (Y3) The exception: Z answers t₃ and moves next, trailing by b₁.
      rw [amtReply_top_tie hU hex]
      have he := hex.1
      have hne32 : ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'' ≠
          (T.erase (T.max' h)).max' hU := Nat.ne_of_lt ht32
      have h3U : ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'' ∈
          T.erase (T.max' h) := Finset.mem_of_mem_erase (Finset.max'_mem _ hT'')
      have hc3 := Finset.card_erase_add_one h3U
      refine ⟨fun hc => absurd hc (by omega), fun _ => ⟨fun h0 => by omega, ?_, fun h4' => ?_⟩⟩
      · intro h' h'' _
        have hmax : ((T.erase (T.max' h)).erase
            (((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'')).max' h' =
            (T.erase (T.max' h)).max' hU := max'_erase_of_ne hU hne32 h'
        have hx := Finset.max'_mem _ h''
        set x := (((T.erase (T.max' h)).erase
            (((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'')).erase
            (((T.erase (T.max' h)).erase
            (((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'')).max' h')).max'
            h''
          with hx_def
        rw [hmax] at hx ⊢
        have hx1 := Finset.mem_erase.mp hx
        have hx2 := Finset.mem_erase.mp (hx1.2)
        have hxT : x ∈ (T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU) :=
          Finset.mem_erase.mpr ⟨hx1.1, hx2.2⟩
        have hxle := Finset.le_max' _ x hxT
        have hxlt : x < ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'' :=
          lt_of_le_of_ne hxle hx2.1
        omega
      · have h' : ((T.erase (T.max' h)).erase
            (((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'')).Nonempty := by
          rw [← Finset.card_pos]; omega
        have hmax : ((T.erase (T.max' h)).erase
            (((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'')).max' h' =
            (T.erase (T.max' h)).max' hU := max'_erase_of_ne hU hne32 h'
        have hZ : depthZ ((T.erase (T.max' h)).erase
            (((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).max' hT'')) =
            depthZ ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)) := by
          rw [depthZ_of_nonempty h', depthZ_of_nonempty hT'', hmax, Finset.erase_right_comm]
        rw [hZ]
        omega
    · -- (Y2) Z answers t₂.
      rw [amtReply_top_no_tie hU hex]
      have hne : e + (T.erase (T.max' h)).max' hU ≠ T.max' h := fun he => hex ⟨he, hT''⟩
      constructor
      · intro hc
        by_cases h2'' : ((T.erase (T.max' h)).erase ((T.erase (T.max' h)).max' hU)).card = 2
        · exact kyc_two_of_depth h2'' (by omega) (by omega)
        · exact ⟨fun _ _ h2''' => absurd h2''' h2'', fun h4' => ⟨by omega, fun _ => by omega⟩⟩
      · intro hc
        refine ⟨fun h0 => by omega, fun h' h'' h2'' => ?_, fun h4' => by omega⟩
        -- The last round: T'' = {t₃, t₄} has t₃ - t₄ - 1 holes.
        have hcs := card_erase_max' h'
        have hcm := card_holes_eq h' h''
        rw [holes_of_card_le_one (U := ((T.erase (T.max' h)).erase
          ((T.erase (T.max' h)).max' hU)).erase (((T.erase (T.max' h)).erase
          ((T.erase (T.max' h)).max' hU)).max' h')) (by omega), Finset.card_empty] at hcm
        have ht43 := max'_erase_lt h' h''
        omega
  · -- (Y1) The opponent takes a lower number; Z takes t₁.
    rw [amtReply_of_ne_max h hi hit hUi e]
    have hlt : i < T.max' h := lt_of_le_of_ne (Finset.le_max' T i hi) hit
    have hiU : i ∈ T.erase (T.max' h) := Finset.mem_erase.mpr ⟨hit, hi⟩
    have hit2 : i ≤ (T.erase (T.max' h)).max' hU := Finset.le_max' _ i hiU
    rw [Finset.erase_right_comm]
    have hB := depth_erase_le hU hiU
    have hUT := depth_erase_max' h
    have hci := Finset.card_erase_add_one hiU
    refine ⟨fun _ => ?_, fun hc => absurd (by omega) hc⟩
    by_cases h2' : ((T.erase (T.max' h)).erase i).card = 2
    · exact kyc_two_of_depth h2' (by omega) (by omega)
    · exact ⟨fun _ _ h2'' => absurd h2'' h2', fun h4' => ⟨by omega, fun _ => by omega⟩⟩

private theorem card_two' {T : Finset ℕ} (hev : Even T.card) {a b : ℕ} (ha : a ∈ T)
    (hb : b ∈ T.erase a) :
    ((T.erase a).erase b).card < T.card ∧ Even ((T.erase a).erase b).card := by
  have h1 := Finset.card_erase_add_one ha
  have h2 := Finset.card_erase_add_one hb
  obtain ⟨k, hk⟩ := hev
  exact ⟨by omega, ⟨k - 1, by omega⟩⟩

/-- **C23.** From C23's classes, Z playing AM+T secures a final margin of at least `-1`: Z's
minimax margin is `≥ -1` where Z moves, and the opponent's is `≤ 1` where it moves. -/
theorem depth_class_roundsMargin (n : ℕ) : ∀ T : Finset ℕ, T.card = n → Even n →
    (∀ d, KZc T d → -1 ≤ roundsMargin T d) ∧ (∀ e, KYc T e → roundsMargin T e ≤ 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn hev
  subst hn
  by_cases h0 : T = ∅
  · subst h0
    refine ⟨fun d hK => ?_, fun e _ => ?_⟩
    · have := hK.1 rfl
      rw [roundsMargin]
      simp only [Finset.not_nonempty_empty, ↓reduceDIte]
      omega
    · rw [roundsMargin]
      simp only [Finset.not_nonempty_empty, ↓reduceDIte]
      omega
  have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
  constructor
  · intro d hK
    have key := neg_le_roundsMargin hev d (Finset.max'_mem T hne) 1 ?_
    · linarith
    intro j hj
    obtain ⟨hlt2, hev2⟩ := card_two' hev (Finset.max'_mem T hne) hj
    obtain ⟨hIZ, hIY⟩ := ih _ hlt2 _ rfl hev2
    obtain ⟨hc1, hc2⟩ := closeZ hev hne hK hj
    by_cases hc : T.max' hne ≤ d + j
    · simp only [hc, ite_true]
      have := hIZ _ (hc1 hc)
      linarith
    · simp only [hc, ite_false]
      exact hIY _ (hc2 hc)
  · intro e hK
    have key := roundsMargin_le_neg hev hne e (-1) ?_
    · linarith
    intro i hi
    have hj := amtReply_mem (erase_nonempty_of_even hev hi) e i
    refine ⟨amtReply (T.erase i) e i, hj, ?_⟩
    obtain ⟨hlt2, hev2⟩ := card_two' hev hi hj
    obtain ⟨hIZ, hIY⟩ := ih _ hlt2 _ rfl hev2
    obtain ⟨hc1, hc2⟩ := closeY hev hK hi
    by_cases hc : i ≤ e + amtReply (T.erase i) e i
    · simp only [hc, ite_true]
      have := hIY _ (hc1 hc)
      linarith
    · simp only [hc, ite_false]
      exact hIZ _ (hc2 hc)

theorem holes_range (n : ℕ) : holes (Finset.range n) = ∅ := by
  by_cases h : (Finset.range n).Nonempty
  · ext x
    simp only [Finset.notMem_empty, iff_false]
    rw [mem_holes h]
    rintro ⟨-, h2, h3⟩
    have := Finset.mem_range.mp (Finset.max'_mem _ h)
    exact h3 (Finset.mem_range.mpr (by omega))
  · simp [holes, h]

theorem depthZ_range (n : ℕ) : depthZ (Finset.range n) = 0 := by
  by_cases h : (Finset.range n).Nonempty
  · rw [depthZ_of_nonempty h]
    have := depth_erase_max' h
    rw [depth_eq_zero_of_holes (holes_range n)] at this
    omega
  · simp [depthZ, h]

/-- The interval `{0..2p-1}`: Z trailing by `d ≤ p` is in C23's class. -/
theorem kzc_range {p : ℕ} (hp : 1 ≤ p) {d : ℕ} (hd : d ≤ p) : KZc (Finset.range (2 * p)) d := by
  refine ⟨fun h0 => by simp at h0; omega, fun h h' h2 => ?_, fun _ => ?_⟩
  · have hlt := max'_erase_lt h h'
    have : p = 1 := by simp at h2; omega
    omega
  · rw [depthZ_range, Finset.card_range]
    omega

/-- The interval `{0..2p-1}`: the opponent moving, trailing by any `e`, is in C23's class. -/
theorem kyc_range (p e : ℕ) : KYc (Finset.range (2 * p)) e := by
  refine ⟨fun h h' h2 => ?_, fun _ => ⟨?_, fun hh => ?_⟩⟩
  · have h1 := Finset.mem_range.mp (Finset.max'_mem _ h)
    have h3 := Finset.mem_range.mp (Finset.mem_of_mem_erase (Finset.max'_mem _ h'))
    simp at h2
    omega
  · rw [depth_eq_zero_of_holes (holes_range _)]
    omega
  · rw [holes_range] at hh
    exact absurd hh Finset.not_nonempty_empty

end CatchUp
