module

public import CatchUp.Linear
public import CatchUp.CostParity

/-!
# Hyb2T: blocks down to height 2p − 1

Z's strategy Hyb2T on an even set `T` of offsets, playing the rounds game (blueprint L25): Z takes
the largest element; Y's pick `i` is answered by the smallest *valid* `j` (one after which Y's
debt is at least the remaining cost), else by AM+T's answer. The potential `potW` never rises
(`potW_z_round`, `potW_y_round`), which gives the block draws at `a ≥ 2p − 1` (L24,
`block_row_draw_hyb2`, `block_draw_hyb2`).

Zone language, index-free: a *bottom* is an element with `OddBelow T` (odd rank), a *top* one
without; `oddPts T x y` counts the odd points of `[x, y)`; `eta T` counts the even holes, points
of `[lo T, hi T)` outside `T` without `OddBelow T`.
-/

@[expose] public section

namespace CatchUp

/-! ## Definitions -/

/-- `O_T(x, y)`: points of `[x, y)` with an odd number of elements of `T` at or below them. -/
noncomputable def oddPts (T : Finset ℕ) (x y : ℕ) : ℕ := ((Finset.Ico x y).filter (OddBelow T)).card

/-- `E_T(x, y)`: the other points of `[x, y)`. -/
noncomputable def evenPts (T : Finset ℕ) (x y : ℕ) : ℕ :=
  ((Finset.Ico x y).filter (fun z => ¬ OddBelow T z)).card

/-- Elements of `T` strictly below `z`. -/
noncomputable def below (T : Finset ℕ) (z : ℕ) : ℕ := (T.filter (· < z)).card

/-- Least element, `0` for the empty set. -/
noncomputable def lo (T : Finset ℕ) : ℕ := if h : T.Nonempty then T.min' h else 0

/-- Greatest element, `0` for the empty set. -/
noncomputable def hi (T : Finset ℕ) : ℕ := if h : T.Nonempty then T.max' h else 0

/-- Second smallest element (`o₂`), `0` if there is none. -/
noncomputable def second (T : Finset ℕ) : ℕ := lo (T.erase (lo T))

/-- η: even holes, points of `[lo T, hi T)` outside `T` without `OddBelow T`. -/
noncomputable def eta (T : Finset ℕ) : ℕ :=
  ((Finset.Ico (lo T) (hi T)).filter (fun z => z ∉ T ∧ ¬ OddBelow T z)).card

/-- Ψ(T) = 2·span − |T| + 2 − o₂. -/
noncomputable def psi (T : Finset ℕ) : ℤ := 2 * ((hi T : ℤ) - lo T) - T.card + 2 - second T

/-- W at a round start: `zMoves` with Z trailing by `d`, else Y trailing by `d`. -/
noncomputable def potW (T : Finset ℕ) (d : ℕ) (zMoves : Bool) : ℤ :=
  if zMoves ∨ (d : ℤ) < matchCost T then psi T
  else max ((d : ℤ) - lo T) (min ((d : ℤ) + matchCost T - second T) (psi T))

/-- Hyb2T's valid answers (L24): the opponent stays mover and lost by L20. -/
def ValidAnswer (T : Finset ℕ) (e i j : ℕ) : Prop :=
  i ≤ e + j ∧ matchCost ((T.erase i).erase j) ≤ ((e + j - i : ℕ) : ℤ)

open Classical in
/-- Hyb2T's answer: the smallest valid answer, else AM+T's. -/
noncomputable def hyb2Reply (T : Finset ℕ) (e i : ℕ) : ℕ :=
  if h : ((T.erase i).filter (ValidAnswer T e i)).Nonempty then
    ((T.erase i).filter (ValidAnswer T e i)).min' h
  else amtReply (T.erase i) e i

/-! ## Extremes -/

theorem lo_of_nonempty {T : Finset ℕ} (h : T.Nonempty) : lo T = T.min' h := by simp [lo, h]

theorem hi_of_nonempty {T : Finset ℕ} (h : T.Nonempty) : hi T = T.max' h := by simp [hi, h]

theorem lo_le {T : Finset ℕ} {x : ℕ} (hx : x ∈ T) : lo T ≤ x := by
  rw [lo_of_nonempty ⟨x, hx⟩]; exact T.min'_le x hx

theorem le_hi {T : Finset ℕ} {x : ℕ} (hx : x ∈ T) : x ≤ hi T := by
  rw [hi_of_nonempty ⟨x, hx⟩]; exact T.le_max' x hx

theorem lo_mem {T : Finset ℕ} (h : T.Nonempty) : lo T ∈ T := by
  rw [lo_of_nonempty h]; exact T.min'_mem h

theorem hi_mem {T : Finset ℕ} (h : T.Nonempty) : hi T ∈ T := by
  rw [hi_of_nonempty h]; exact T.max'_mem h

theorem lo_le_lo_of_subset {T T' : Finset ℕ} (hsub : T' ⊆ T) (h : T'.Nonempty) : lo T ≤ lo T' :=
  lo_le (hsub (lo_mem h))

theorem hi_le_hi_of_subset {T T' : Finset ℕ} (hsub : T' ⊆ T) : hi T' ≤ hi T := by
  by_cases h : T'.Nonempty
  · exact le_hi (hsub (hi_mem h))
  · simp [hi, h]

/-- Dropping the least element raises the least element. -/
theorem lo_lt_lo_of_subset {T T' : Finset ℕ} (hsub : T' ⊆ T) (h : T'.Nonempty) (hn : lo T ∉ T') :
    lo T < lo T' := by
  refine lt_of_le_of_ne (lo_le_lo_of_subset hsub h) fun he => hn ?_
  rw [he]; exact lo_mem h

/-- Dropping the greatest element lowers the greatest element. -/
theorem hi_lt_hi_of_subset {T T' : Finset ℕ} (hsub : T' ⊆ T) (h : T'.Nonempty) (hn : hi T ∉ T') :
    hi T' < hi T := by
  refine lt_of_le_of_ne (hi_le_hi_of_subset hsub) fun he => hn ?_
  rw [← he]; exact hi_mem h

theorem second_le {T : Finset ℕ} {w : ℕ} (hw : w ∈ T) (hne : w ≠ lo T) : second T ≤ w :=
  lo_le (Finset.mem_erase.mpr ⟨hne, hw⟩)

theorem second_mem {T : Finset ℕ} (h2 : 2 ≤ T.card) : second T ∈ T.erase (lo T) := by
  apply lo_mem
  rw [← Finset.card_pos, Finset.card_erase_of_mem (lo_mem (Finset.card_pos.mp (by omega)))]
  omega

/-- A subset with at least two elements has at most one element, `lo T`, below `second T`. -/
theorem second_le_second_of_subset {T T' : Finset ℕ} (hsub : T' ⊆ T) (h2 : 2 ≤ T'.card) :
    second T ≤ second T' := by
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp (second_mem h2)
  apply second_le (hsub hmem)
  intro he
  have h1 : lo T ≤ lo T' := lo_le_lo_of_subset hsub (Finset.card_pos.mp (by omega))
  have h3 : lo T' ≤ second T' := lo_le hmem
  exact hne (by omega)

/-! ## Counting below a point -/

theorem card_filter_lt_succ (T : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (z : ℕ) :
    ((T.filter (· < z + 1)).filter P).card =
      ((T.filter (· < z)).filter P).card + if z ∈ T ∧ P z then 1 else 0 := by
  split_ifs with h
  · have hs : (T.filter (· < z + 1)).filter P = insert z ((T.filter (· < z)).filter P) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨⟨hw, hlt⟩, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h' | h'
        · exact Or.inr ⟨⟨hw, h'⟩, hp⟩
        · exact Or.inl h'
      · rintro (rfl | ⟨⟨hw, hlt⟩, hp⟩)
        · exact ⟨⟨h.1, by omega⟩, h.2⟩
        · exact ⟨⟨hw, by omega⟩, hp⟩
    rw [hs, Finset.card_insert_of_notMem (by simp)]
  · rw [add_zero]
    congr 1
    ext w
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hw, hlt⟩, hp⟩
      refine ⟨⟨hw, ?_⟩, hp⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h' | h'
      · exact h'
      · subst h'; exact absurd ⟨hw, hp⟩ h
    · rintro ⟨⟨hw, hlt⟩, hp⟩
      exact ⟨⟨hw, by omega⟩, hp⟩

theorem below_succ (T : Finset ℕ) (z : ℕ) :
    below T (z + 1) = below T z + if z ∈ T then 1 else 0 := by
  have h := card_filter_lt_succ T (fun _ => True) z
  simpa [below, Finset.filter_true_of_mem] using h

theorem card_filter_le_eq_below_succ (T : Finset ℕ) (z : ℕ) :
    (T.filter (· ≤ z)).card = below T (z + 1) := by
  unfold below
  exact congrArg Finset.card (Finset.filter_congr fun x _ => Nat.lt_succ_iff.symm)

/-- An element's rank is one more than the number of elements below it. -/
theorem oddBelow_iff_of_mem {T : Finset ℕ} {z : ℕ} (hz : z ∈ T) :
    OddBelow T z ↔ (below T z + 1) % 2 = 1 := by
  unfold OddBelow
  rw [card_filter_le_eq_below_succ, below_succ, ite_eq_left hz, Nat.odd_iff]

/-- No point below the least element is odd. -/
theorem not_oddBelow_of_lt_lo {T : Finset ℕ} {x : ℕ} (hx : x < lo T) : ¬ OddBelow T x := by
  unfold OddBelow
  have : T.filter (· ≤ x) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun y hy hyx => by have := lo_le hy; omega
  rw [this]
  simp

/-! ## Zone tools (L25 part 3, A–C) -/

/-- Alternation: below `z`, bottoms minus tops is 1 or 0 as the number of elements below `z` is
odd or even. -/
theorem bottoms_sub_tops (T : Finset ℕ) (z : ℕ) :
    (((T.filter (· < z)).filter (OddBelow T)).card : ℤ) -
      ((T.filter (· < z)).filter (fun o => ¬ OddBelow T o)).card =
      if Odd (below T z) then 1 else 0 := by
  induction z with
  | zero => simp [below]
  | succ z ih =>
    rw [card_filter_lt_succ, card_filter_lt_succ, below_succ]
    simp only [Nat.odd_iff] at ih ⊢
    by_cases hz : z ∈ T
    · have hob := oddBelow_iff_of_mem hz
      by_cases hp : OddBelow T z
      · have h1 := hob.mp hp
        simp only [hz, hp, not_true_eq_false, and_self, and_false, ↓reduceIte]
        split_ifs at ih ⊢ <;> push_cast <;> omega
      · have h1 : ¬ (below T z + 1) % 2 = 1 := fun h => hp (hob.mpr h)
        simp only [hz, hp, not_false_eq_true, and_self, and_false, ↓reduceIte]
        split_ifs at ih ⊢ <;> push_cast <;> omega
    · simp only [hz, false_and, ↓reduceIte, add_zero]
      exact ih

/-- (A3) The cost counts the odd points between the extremes. -/
theorem matchCost_eq_oddPts {T : Finset ℕ} (hev : Even T.card) :
    matchCost T = oddPts T (lo T) (hi T) := by
  rw [matchCost_eq_card_odd _ T rfl hev (hi T) fun o ho => le_hi ho]
  unfold oddPts
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hx, hp⟩
    refine ⟨⟨?_, hx⟩, hp⟩
    by_contra hlt
    exact not_oddBelow_of_lt_lo (by omega) hp
  · rintro ⟨⟨-, hx⟩, hp⟩
    exact ⟨hx, hp⟩

/-- (A3)/(D1) span = c + η + (k − 1), so Ψ = 2(c + η) − o₂. -/
theorem psi_eq {T : Finset ℕ} (hev : Even T.card) (h2 : 2 ≤ T.card) :
    psi T = 2 * (matchCost T + eta T) - second T := by
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hlohi : lo T ≤ hi T := lo_le (hi_mem hne)
  -- span = odd points + even points of `[lo T, hi T)`
  have hspan : hi T - lo T = oddPts T (lo T) (hi T) + evenPts T (lo T) (hi T) := by
    unfold oddPts evenPts
    rw [Finset.card_filter_add_card_filter_not, Nat.card_Ico]
  -- even points = tops other than `hi T` + even holes
  have heven : evenPts T (lo T) (hi T) =
      ((T.filter (· < hi T)).filter (fun o => ¬ OddBelow T o)).card + eta T := by
    unfold evenPts eta
    rw [← Finset.card_filter_add_card_filter_not
      (s := (Finset.Ico (lo T) (hi T)).filter (fun z => ¬ OddBelow T z)) (· ∈ T)]
    congr 1
    · congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨⟨-, hz⟩, hp⟩, hm⟩
        exact ⟨⟨hm, hz⟩, hp⟩
      · rintro ⟨⟨hm, hz⟩, hp⟩
        exact ⟨⟨⟨lo_le hm, hz⟩, hp⟩, hm⟩
    · congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_Ico]
      tauto
  -- the elements below `hi T` alternate bottom, top, ..., bottom: `k - 1` tops
  have hbelow : below T (hi T) + 1 = T.card := by
    unfold below
    have : T.filter (· < hi T) = T.erase (hi T) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hw, hlt⟩; exact ⟨by omega, hw⟩
      · rintro ⟨hne', hw⟩; exact ⟨hw, lt_of_le_of_ne (le_hi hw) hne'⟩
    rw [this]
    exact Finset.card_erase_add_one (hi_mem hne)
  obtain ⟨r, hr⟩ := hev
  have hodd : Odd (below T (hi T)) := ⟨r - 1, by omega⟩
  have hbt := bottoms_sub_tops T (hi T)
  rw [ite_eq_left hodd] at hbt
  have hsum := Finset.card_filter_add_card_filter_not (s := T.filter (· < hi T)) (OddBelow T)
  rw [matchCost_eq_oddPts ⟨r, hr⟩]
  unfold psi
  unfold below at hbelow
  omega

/-- (D2) Removing two elements, one of them the least or the greatest, does not raise Ψ. -/
theorem psi_erase_two_le {T : Finset ℕ} {x y : ℕ} (hx : x ∈ T) (hy : y ∈ T.erase x)
    (hext : x = lo T ∨ x = hi T ∨ y = lo T ∨ y = hi T) (h2 : 2 ≤ ((T.erase x).erase y).card) :
    psi ((T.erase x).erase y) ≤ psi T := by
  have hsub : (T.erase x).erase y ⊆ T := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hne : ((T.erase x).erase y).Nonempty := Finset.card_pos.mp (by omega)
  have hc : ((T.erase x).erase y).card + 2 = T.card := by
    have := Finset.card_erase_add_one hx
    have := Finset.card_erase_add_one hy
    omega
  have hxn : x ∉ (T.erase x).erase y := fun h =>
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase h)).1 rfl
  have hyn : y ∉ (T.erase x).erase y := Finset.notMem_erase y _
  have hs := second_le_second_of_subset hsub h2
  have hlo := lo_le_lo_of_subset hsub hne
  have hhi := hi_le_hi_of_subset hsub
  have key : lo T < lo ((T.erase x).erase y) ∨ hi ((T.erase x).erase y) < hi T := by
    rcases hext with h | h | h | h
    · exact Or.inl (lo_lt_lo_of_subset hsub hne (h ▸ hxn))
    · exact Or.inr (hi_lt_hi_of_subset hsub hne (h ▸ hxn))
    · exact Or.inl (lo_lt_lo_of_subset hsub hne (h ▸ hyn))
    · exact Or.inr (hi_lt_hi_of_subset hsub hne (h ▸ hyn))
  unfold psi
  omega

set_option linter.unusedVariables false in
/-- o₂ never decreases when two elements are removed. -/
theorem second_le_second_erase_two {T : Finset ℕ} {x y : ℕ} (hx : x ∈ T) (hy : y ∈ T.erase x)
    (h2 : 2 ≤ ((T.erase x).erase y).card) :
    second T ≤ second ((T.erase x).erase y) :=
  second_le_second_of_subset ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) h2

/-! ## Counting above the second smallest -/

/-- The elements other than the two smallest lie in `(o₂, max]`, so there are at most
`max − o₂` of them. -/
theorem card_le_hi_sub_second {T : Finset ℕ} (h2 : 2 ≤ T.card) :
    T.card ≤ hi T - second T + 2 := by
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hl := lo_mem hne
  have hc1 := Finset.card_erase_add_one hl
  have hne' : (T.erase (lo T)).Nonempty := Finset.card_pos.mp (by omega)
  have hs : second T ∈ T.erase (lo T) := lo_mem hne'
  have hc2 := Finset.card_erase_add_one hs
  have hsub : (T.erase (lo T)).erase (second T) ⊆ Finset.Ioc (second T) (hi T) := by
    intro x hx
    have hx1 := Finset.mem_erase.mp hx
    have hx2 := Finset.mem_erase.mp hx1.2
    have h1 : second T ≤ x := lo_le hx1.2
    exact Finset.mem_Ioc.mpr ⟨lt_of_le_of_ne h1 (Ne.symm hx1.1), le_hi hx2.2⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at this
  omega

/-! ## Zone facts used by Y's rounds (index-free forms of L25's (A), (C), (F)) -/

/-- Consecutive elements: between `p < j` in `T` with nothing of `T` strictly between, the parity
is that of `p`, and it flips at `j`. -/
theorem oddBelow_consec {T : Finset ℕ} {p j : ℕ} (hj : j ∈ T) (hpj : p < j)
    (hgap : ∀ x ∈ T, ¬ (p < x ∧ x < j)) :
    (∀ z, p ≤ z → z < j → (OddBelow T z ↔ OddBelow T p)) ∧ (OddBelow T j ↔ ¬ OddBelow T p) := by
  have hle : ∀ z, p ≤ z → z < j → T.filter (· ≤ z) = T.filter (· ≤ p) := by
    intro z hpz hzj
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hxz⟩
      refine ⟨hx, ?_⟩
      by_contra hxp
      exact hgap x hx ⟨by omega, by omega⟩
    · rintro ⟨hx, hxp⟩
      exact ⟨hx, by omega⟩
  refine ⟨fun z hpz hzj => by unfold OddBelow; rw [hle z hpz hzj], ?_⟩
  have hj' : T.filter (· ≤ j) = insert j (T.filter (· ≤ p)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hxj⟩
      by_cases hxe : x = j
      · exact Or.inl hxe
      · refine Or.inr ⟨hx, ?_⟩
        by_contra hxp
        exact hgap x hx ⟨by omega, by omega⟩
    · rintro (rfl | ⟨hx, hxp⟩)
      · exact ⟨hj, le_rfl⟩
      · exact ⟨hx, by omega⟩
  have hnot : j ∉ T.filter (· ≤ p) := by simp; omega
  unfold OddBelow
  rw [hj', Finset.card_insert_of_notMem hnot, Nat.odd_add_one]

/-- Alternation on `[x, y)` for `x < y` in `T`: bottoms minus tops is `[y top] − [x top]`. -/
theorem bottoms_sub_tops_Ico {T : Finset ℕ} {x y : ℕ} (hx : x ∈ T) (hy : y ∈ T) (hxy : x < y) :
    ((((T.filter (fun o => x ≤ o ∧ o < y)).filter (OddBelow T)).card : ℤ) -
      ((T.filter (fun o => x ≤ o ∧ o < y)).filter (fun o => ¬ OddBelow T o)).card) =
      (if OddBelow T y then 0 else 1) - (if OddBelow T x then 0 else 1) := by
  -- Elements below `y` split into those in `[x, y)` and those below `x`.
  have split : ∀ (P : ℕ → Prop) [DecidablePred P],
      ((T.filter (fun o => x ≤ o ∧ o < y)).filter P).card + ((T.filter (· < x)).filter P).card =
        ((T.filter (· < y)).filter P).card := by
    intro P _
    have e1 : ((T.filter (· < y)).filter P).filter (fun o => x ≤ o) =
        (T.filter (fun o => x ≤ o ∧ o < y)).filter P := by
      ext o
      simp only [Finset.mem_filter]
      tauto
    have e2 : ((T.filter (· < y)).filter P).filter (fun o => ¬ x ≤ o) =
        (T.filter (· < x)).filter P := by
      ext o
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨⟨ho, -⟩, hp⟩, hox⟩
        exact ⟨⟨ho, by omega⟩, hp⟩
      · rintro ⟨⟨ho, hox⟩, hp⟩
        exact ⟨⟨⟨ho, by omega⟩, hp⟩, by omega⟩
    rw [← Finset.card_filter_add_card_filter_not (s := (T.filter (· < y)).filter P)
      (p := fun o => x ≤ o), e1, e2]
  have hb := split (OddBelow T)
  have ht := split (fun o => ¬ OddBelow T o)
  have hy' := bottoms_sub_tops T y
  have hx' := bottoms_sub_tops T x
  have hoy : Odd (below T y) ↔ ¬ OddBelow T y := by
    rw [oddBelow_iff_of_mem hy, Nat.odd_iff]; omega
  have hox : Odd (below T x) ↔ ¬ OddBelow T x := by
    rw [oddBelow_iff_of_mem hx, Nat.odd_iff]; omega
  by_cases h1 : OddBelow T y <;> by_cases h2 : OddBelow T x <;>
    simp only [h1, h2, hoy, hox, not_true_eq_false, not_false_eq_true, ↓reduceIte] at hy' hx' ⊢ <;>
    omega

/-- Even points split into tops and even holes; inside `[lo, hi)` the holes are at most η. -/
theorem evenPts_le_tops_add_eta {T : Finset ℕ} {x y : ℕ} (hx : lo T ≤ x) (hy : y ≤ hi T) :
    (evenPts T x y : ℤ) ≤
      ((T.filter (fun o => x ≤ o ∧ o < y)).filter (fun o => ¬ OddBelow T o)).card + eta T := by
  -- Even points of `[x, y)`: those in `T` (tops) and the rest (even holes inside `[lo, hi)`).
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.Ico x y).filter (fun z => ¬ OddBelow T z)) (p := fun z => z ∈ T)
  have e1 : ((Finset.Ico x y).filter (fun z => ¬ OddBelow T z)).filter (fun z => z ∈ T) =
      (T.filter (fun o => x ≤ o ∧ o < y)).filter (fun o => ¬ OddBelow T o) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_Ico]
    tauto
  have h2 : (((Finset.Ico x y).filter (fun z => ¬ OddBelow T z)).filter (fun z => z ∉ T)).card ≤
      eta T := by
    unfold eta
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_Ico] at hz ⊢
    exact ⟨⟨by omega, by omega⟩, hz.2, hz.1.2⟩
  rw [e1] at hsplit
  unfold evenPts
  omega

/-- Odd points include the bottoms. -/
theorem bottoms_le_oddPts (T : Finset ℕ) (x y : ℕ) :
    ((T.filter (fun o => x ≤ o ∧ o < y)).filter (OddBelow T)).card ≤ oddPts T x y := by
  unfold oddPts
  apply Finset.card_le_card
  intro o ho
  simp only [Finset.mem_filter] at ho
  simp only [Finset.mem_filter, Finset.mem_Ico]
  exact ⟨⟨ho.1.2.1, ho.1.2.2⟩, ho.2⟩

/-- (C1) The cost has the parity of the sum. -/
theorem matchCost_parity {T : Finset ℕ} (hev : Even T.card) :
    (matchCost T - ∑ o ∈ T, (o : ℤ)) % 2 = 0 := by
  suffices h : ∀ n, ∀ O : Finset ℕ, O.card = n → Even n →
      (matchCost O - ∑ o ∈ O, (o : ℤ)) % 2 = 0 from h _ T rfl hev
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro O hn hevn
  by_cases h : O.Nonempty
  · obtain ⟨a, ha, hamin⟩ : ∃ a ∈ O, ∀ x ∈ O, a ≤ x :=
      ⟨O.min' h, Finset.min'_mem O h, fun x hx => Finset.min'_le O x hx⟩
    have h' := erase_nonempty_of_even (hn ▸ hevn) ha
    obtain ⟨b, hbE, hbmin⟩ : ∃ b ∈ O.erase a, ∀ x ∈ O.erase a, b ≤ x :=
      ⟨(O.erase a).min' h', Finset.min'_mem _ h', fun x hx => Finset.min'_le _ x hx⟩
    have hb := Finset.mem_of_mem_erase hbE
    have hab : a < b := lt_of_le_of_ne (hamin b hb) (Finset.mem_erase.mp hbE).1.symm
    have hmin : ∀ x ∈ O, x = a ∨ b ≤ x := by
      intro x hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      · exact Or.inr (hbmin x (Finset.mem_erase.mpr ⟨hxa, hx⟩))
    have h1 := Finset.card_erase_add_one ha
    have h2 := Finset.card_erase_add_one hbE
    obtain ⟨k, hk⟩ := hevn
    have hlt : ((O.erase a).erase b).card < n := by omega
    have ih' := ih _ hlt _ rfl ⟨k - 1, by omega⟩
    rw [matchCost_of_min ha hb hab hmin]
    have hs1 := Finset.sum_erase_add O (fun o => (o : ℤ)) ha
    have hs2 := Finset.sum_erase_add (O.erase a) (fun o => (o : ℤ)) hbE
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, matchCost_empty]
    simp

/-- (F) Removing `i ≠ j`: the cost changes by `|j − i|` minus twice the odd points between. -/
theorem matchCost_erase_pair {T : Finset ℕ} (hev : Even T.card) {i j : ℕ} (hiT : i ∈ T)
    (hj : j ∈ T.erase i) :
    matchCost ((T.erase i).erase j) =
      matchCost T + |(j : ℤ) - i| - 2 * oddPts T (min i j) (max i j) := by
  have hjT := Finset.mem_of_mem_erase hj
  have hne : i ≠ j := (Finset.ne_of_mem_erase hj).symm
  have hM : ∀ o ∈ T, o ≤ hi T := fun o ho => le_hi ho
  rcases lt_or_gt_of_ne hne with hij | hji
  · have := matchCost_erase_two hev hiT hj hij hM
    rw [min_eq_left hij.le, max_eq_right hij.le, abs_of_nonneg (by omega)]
    unfold oddPts
    linarith
  · have hiE : i ∈ T.erase j := Finset.mem_erase.mpr ⟨hne, hiT⟩
    have := matchCost_erase_two hev hjT hiE hji hM
    rw [Finset.erase_right_comm] at this
    rw [min_eq_right hji.le, max_eq_left hji.le, abs_of_neg (by omega)]
    unfold oddPts
    linarith

/-- Validity is the cost inequality alone (the debt condition follows, costs being `≥ 0`). -/
theorem validAnswer_iff {T : Finset ℕ} {e i j : ℕ} :
    ValidAnswer T e i j ↔ matchCost ((T.erase i).erase j) ≤ (e : ℤ) + j - i := by
  have h0 := matchCost_nonneg _ ((T.erase i).erase j) rfl
  unfold ValidAnswer
  constructor
  · rintro ⟨hle, hc⟩
    push_cast [hle] at hc
    linarith
  · intro hc
    have hle : i ≤ e + j := by omega
    refine ⟨hle, ?_⟩
    push_cast [hle]
    linarith

open Classical in
/-- Hyb2T's answer, when some answer is valid, is valid and below every valid answer. -/
theorem hyb2Reply_min {T : Finset ℕ} {e i j : ℕ} (hj : j ∈ T.erase i) (hv : ValidAnswer T e i j) :
    hyb2Reply T e i ∈ T.erase i ∧ ValidAnswer T e i (hyb2Reply T e i) ∧ hyb2Reply T e i ≤ j := by
  have hne : ((T.erase i).filter (ValidAnswer T e i)).Nonempty :=
    ⟨j, Finset.mem_filter.mpr ⟨hj, hv⟩⟩
  have hdef : hyb2Reply T e i = ((T.erase i).filter (ValidAnswer T e i)).min' hne := by
    unfold hyb2Reply
    simp only [hne, ↓reduceDIte]
  rw [hdef]
  have hmem := Finset.mem_filter.mp (Finset.min'_mem _ hne)
  exact ⟨hmem.1, hmem.2, Finset.min'_le _ j (Finset.mem_filter.mpr ⟨hj, hv⟩)⟩

open Classical in
/-- With no valid answer, Hyb2T answers AM+T, and the pair taken contains the greatest. -/
theorem hyb2Reply_fallback {T : Finset ℕ} (hev : Even T.card) {e i : ℕ} (hiT : i ∈ T)
    (hnone : ∀ j ∈ T.erase i, ¬ ValidAnswer T e i j) :
    hyb2Reply T e i ∈ T.erase i ∧ (i = hi T ∨ hyb2Reply T e i = hi T) := by
  have hne : ¬ ((T.erase i).filter (ValidAnswer T e i)).Nonempty := by
    rintro ⟨j, hj⟩
    exact hnone j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hdef : hyb2Reply T e i = amtReply (T.erase i) e i := by
    unfold hyb2Reply
    simp only [hne, ↓reduceDIte]
  have hU := erase_nonempty_of_even hev hiT
  rw [hdef]
  refine ⟨amtReply_mem hU e i, ?_⟩
  by_cases him : i = hi T
  · exact Or.inl him
  · right
    have hTne : T.Nonempty := ⟨i, hiT⟩
    have hmU : hi T ∈ T.erase i := Finset.mem_erase.mpr ⟨Ne.symm him, hi_mem hTne⟩
    have hmax : (T.erase i).max' hU = hi T :=
      le_antisymm (Finset.max'_le _ _ _ fun x hx => le_hi (Finset.mem_of_mem_erase hx))
        (Finset.le_max' _ _ hmU)
    have hilt : i < hi T := lt_of_le_of_ne (le_hi hiT) him
    have hnt : ¬ (e + hi T = i ∧ ((T.erase i).erase (hi T)).Nonempty) := fun h => by omega
    unfold amtReply
    simp only [hU, ↓reduceDIte, hmax, hnt]

/-- Once Y is lost by L20 (`c ≤ e`), some answer is valid (the partner). -/
theorem exists_valid_of_lost {T : Finset ℕ} (hev : Even T.card) {e i : ℕ} (hiT : i ∈ T)
    (he : matchCost T ≤ e) : ∃ j ∈ T.erase i, ValidAnswer T e i j := by
  obtain ⟨j, hj, hc⟩ := exists_partner T.card T rfl hev i hiT
  refine ⟨j, hj, validAnswer_iff.mpr ?_⟩
  have h1 := le_abs_self ((i : ℤ) - j)
  have h2 := neg_abs_le ((i : ℤ) - j)
  linarith

/-! ## Interval helpers -/

theorem oddPts_add_evenPts (T : Finset ℕ) (x y : ℕ) :
    oddPts T x y + evenPts T x y = y - x := by
  unfold oddPts evenPts
  rw [Finset.card_filter_add_card_filter_not, Nat.card_Ico]

theorem oddPts_trans (T : Finset ℕ) {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) :
    oddPts T x z = oddPts T x y + oddPts T y z := by
  unfold oddPts
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hw : w < y
      · exact Or.inl ⟨⟨h1, hw⟩, h3⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) <;> exact ⟨⟨by omega, by omega⟩, h3⟩
  · rw [Finset.disjoint_left]
    intro w h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ico] at h1 h2
    omega

theorem evenPts_trans (T : Finset ℕ) {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) :
    evenPts T x z = evenPts T x y + evenPts T y z := by
  have h1 := oddPts_add_evenPts T x z
  have h2 := oddPts_add_evenPts T x y
  have h3 := oddPts_add_evenPts T y z
  have h4 := oddPts_trans T hxy hyz
  omega

/-- On a run where every point is odd, all points count. -/
theorem oddPts_of_all {T : Finset ℕ} {x y : ℕ}
    (h : ∀ z, x ≤ z → z < y → OddBelow T z) : oddPts T x y = y - x := by
  have h1 := oddPts_add_evenPts T x y
  have h2 : evenPts T x y = 0 := by
    unfold evenPts
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z hz
    simp only [Finset.mem_Ico] at hz
    exact not_not.mpr (h z hz.1 hz.2)
  omega

/-- On a run where no point is odd, none counts. -/
theorem oddPts_of_none {T : Finset ℕ} {x y : ℕ}
    (h : ∀ z, x ≤ z → z < y → ¬ OddBelow T z) : oddPts T x y = 0 := by
  unfold oddPts
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z hz
  simp only [Finset.mem_Ico] at hz
  exact h z hz.1 hz.2

/-- The element of `T` just below `j`, given one below it. -/
theorem exists_pred {T : Finset ℕ} {i j : ℕ} (hiT : i ∈ T) (hij : i < j) :
    ∃ p ∈ T, i ≤ p ∧ p < j ∧ ∀ x ∈ T, ¬ (p < x ∧ x < j) := by
  have hne : (T.filter (· < j)).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hiT, hij⟩⟩
  set p := (T.filter (· < j)).max' hne
  have hp := Finset.mem_filter.mp (Finset.max'_mem _ hne)
  refine ⟨p, hp.1, Finset.le_max' _ i (Finset.mem_filter.mpr ⟨hiT, hij⟩), hp.2, ?_⟩
  rintro x hx ⟨hpx, hxj⟩
  have := Finset.le_max' (T.filter (· < j)) x (by simp [Finset.mem_filter, hx, hxj])
  omega

/-- The cost bounds the odd points of any run inside `[lo, hi]`. -/
theorem oddPts_le_matchCost {T : Finset ℕ} (hev : Even T.card) {x y : ℕ} (hx : lo T ≤ x)
    (hxy : x ≤ y) (hy : y ≤ hi T) : (oddPts T x y : ℤ) ≤ matchCost T := by
  rw [matchCost_eq_oddPts hev, oddPts_trans T hx (hxy.trans hy), oddPts_trans T hxy hy]
  push_cast
  omega

/-- The least element starts an odd run up to the second smallest. -/
theorem oddPts_lo_second {T : Finset ℕ} (h2 : 2 ≤ T.card) :
    oddPts T (lo T) (second T) = second T - lo T := by
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hlo := lo_mem hne
  have hs := second_mem h2
  have hsT := Finset.mem_of_mem_erase hs
  have hlt : lo T < second T := lt_of_le_of_ne (lo_le hsT) (Finset.ne_of_mem_erase hs).symm
  have hgap : ∀ x ∈ T, ¬ (lo T < x ∧ x < second T) := by
    rintro x hx ⟨h1, h2⟩
    have := second_le hx (by omega)
    omega
  have hodd : OddBelow T (lo T) := by
    rw [oddBelow_iff_of_mem hlo]
    have : below T (lo T) = 0 := by
      unfold below
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      have := lo_le hx
      omega
    omega
  exact oddPts_of_all fun z h1 h2 =>
    ((oddBelow_consec hsT hlt hgap).1 z h1 h2).mpr hodd

/-! ## The claim (L25 part 4) and its five transitions -/

/-- **T1.** Z picks the greatest; whatever Y answers, W does not rise. -/
theorem potW_z_round {T : Finset ℕ} (h4 : 4 ≤ T.card) {d y : ℕ}
    (hy : y ∈ T.erase (hi T)) :
    (hi T ≤ d + y → potW ((T.erase (hi T)).erase y) (d + y - hi T) true ≤ potW T d true) ∧
    (¬ hi T ≤ d + y → potW ((T.erase (hi T)).erase y) (hi T - d - y) false ≤ potW T d true) := by
  have hne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hm := hi_mem hne
  have hc1 := Finset.card_erase_add_one hm
  have hc2 := Finset.card_erase_add_one hy
  have h2' : 2 ≤ ((T.erase (hi T)).erase y).card := by omega
  have hpsi := psi_erase_two_le hm hy (Or.inr (Or.inl rfl)) h2'
  have hW : potW T d true = psi T := by simp [potW]
  rw [hW]
  refine ⟨fun _ => by simpa [potW] using hpsi, fun hlt => ?_⟩
  -- Y moves next, at debt e' = max − d − y ≤ max − lo T; and lo T' ≥ lo T.
  set T' := (T.erase (hi T)).erase y with hT'
  have hne' : T'.Nonempty := Finset.card_pos.mp (by omega)
  have hlo : lo T ≤ lo T' := lo_le_lo_of_subset
    (fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)) hne'
  have hyT : lo T ≤ y := lo_le (Finset.mem_of_mem_erase hy)
  have hcard := card_le_hi_sub_second (T := T) (by omega)
  have hl1 := Finset.card_erase_add_one (lo_mem hne)
  have hne2 : (T.erase (lo T)).Nonempty := Finset.card_pos.mp (by omega)
  have hsmem : second T ∈ T.erase (lo T) := lo_mem hne2
  have hsec : second T ≤ hi T := le_hi (Finset.mem_of_mem_erase hsmem)
  have hX : ((hi T - d - y : ℕ) : ℤ) - lo T' ≤ psi T := by
    unfold psi
    have : d + y ≤ hi T := by omega
    omega
  by_cases hc : ((hi T - d - y : ℕ) : ℤ) < matchCost T'
  · simp only [potW, Bool.false_eq_true, false_or, hc, ↓reduceIte]
    exact hpsi
  · simp only [potW, Bool.false_eq_true, false_or, hc, ↓reduceIte]
    exact max_le hX ((min_le_right _ _).trans hpsi)

/-- **T2.** No valid answer: Y was not lost (`e < c`), Hyb2T's answer takes the greatest with the
pair, and the next start (Z's, or Y's still not lost) has W = Ψ of a set without its greatest. -/
theorem potW_y_round_fallback {T : Finset ℕ} (hev : Even T.card) (h4 : 4 ≤ T.card) {e i : ℕ}
    (hiT : i ∈ T) (hnone : ∀ j ∈ T.erase i, ¬ ValidAnswer T e i j) :
    (i ≤ e + hyb2Reply T e i →
      potW ((T.erase i).erase (hyb2Reply T e i)) (e + hyb2Reply T e i - i) false ≤
        potW T e false) ∧
    (¬ i ≤ e + hyb2Reply T e i →
      potW ((T.erase i).erase (hyb2Reply T e i)) (i - e - hyb2Reply T e i) true ≤
        potW T e false) := by
  obtain ⟨hj, hext⟩ := hyb2Reply_fallback hev hiT hnone
  set j := hyb2Reply T e i with hjdef
  have hlost : (e : ℤ) < matchCost T := by
    by_contra hc
    obtain ⟨j', hj', hv⟩ := exists_valid_of_lost (e := e) hev hiT (by omega)
    exact hnone j' hj' hv
  have hW : potW T e false = psi T := by simp [potW, hlost]
  have hc1 := Finset.card_erase_add_one hiT
  have hc2 := Finset.card_erase_add_one hj
  have hext' : i = lo T ∨ i = hi T ∨ j = lo T ∨ j = hi T := by
    rcases hext with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  have hpsi : psi ((T.erase i).erase j) ≤ psi T := psi_erase_two_le hiT hj hext' (by omega)
  rw [hW]
  refine ⟨fun hle => ?_, fun _ => by simpa [potW] using hpsi⟩
  have hinv := hnone j hj
  rw [validAnswer_iff] at hinv
  have hlt : ((e + j - i : ℕ) : ℤ) < matchCost ((T.erase i).erase j) := by
    push_cast [hle]
    linarith
  simpa [potW, hlt] using hpsi

/-- Validity of an answer above Y's pick: the cost minus twice the odd points between is at most
Y's debt. -/
theorem validAnswer_above_iff {T : Finset ℕ} (hev : Even T.card) {e i x : ℕ} (hiT : i ∈ T)
    (hx : x ∈ T.erase i) (hix : i < x) :
    ValidAnswer T e i x ↔ matchCost T - 2 * oddPts T i x ≤ e := by
  rw [validAnswer_iff, matchCost_erase_pair hev hiT hx, min_eq_left hix.le, max_eq_right hix.le,
    abs_of_nonneg (by omega)]
  constructor <;> intro h <;> linarith

/-- **T3.** Y moves before the switch (`e < c`) and some answer is valid: Hyb2T's answer `j` is
above `i`, the element `p` just below `j` is a bottom, and W does not rise. -/
theorem potW_y_round_switch {T : Finset ℕ} (hev : Even T.card) (h4 : 4 ≤ T.card) {e i : ℕ}
    (hpar : (e + ∑ o ∈ T, o) % 2 = 0) (hiT : i ∈ T) (hlost : (e : ℤ) < matchCost T) {j0 : ℕ}
    (hj0 : j0 ∈ T.erase i) (hv0 : ValidAnswer T e i j0) :
    (i ≤ e + hyb2Reply T e i →
      potW ((T.erase i).erase (hyb2Reply T e i)) (e + hyb2Reply T e i - i) false ≤
        potW T e false) ∧
    (¬ i ≤ e + hyb2Reply T e i →
      potW ((T.erase i).erase (hyb2Reply T e i)) (i - e - hyb2Reply T e i) true ≤
        potW T e false) := by
  obtain ⟨hj, hvj, -⟩ := hyb2Reply_min hj0 hv0
  set j := hyb2Reply T e i with hjdef
  have hjmin : ∀ x ∈ T.erase i, ValidAnswer T e i x → j ≤ x :=
    fun x hx hvx => (hyb2Reply_min hx hvx).2.2
  have hjT := Finset.mem_of_mem_erase hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  refine ⟨fun hle => ?_, fun hle => absurd hvj.1 hle⟩
  -- σ = e − c is even and negative.
  have hσ : ((e : ℤ) - matchCost T) % 2 = 0 := by
    have h1 := matchCost_parity hev
    have h2 : ((e + ∑ o ∈ T, o : ℕ) : ℤ) % 2 = 0 := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hpar
    push_cast at h2
    omega
  -- (P1) The answer is above `i`.
  have hij : i < j := by
    by_contra hc
    have hlt : j < i := lt_of_le_of_ne (not_lt.mp hc) hji
    have hv := validAnswer_iff.mp hvj
    rw [matchCost_erase_pair hev hiT hj, min_eq_right hlt.le, max_eq_left hlt.le,
      abs_of_neg (by omega)] at hv
    have hOE := oddPts_add_evenPts T j i
    omega
  have hvj' := (validAnswer_above_iff hev hiT hj hij).mp hvj
  -- The element `p` just below `j`; it is a bottom.
  obtain ⟨p, hpT, hip, hpj, hgap⟩ := exists_pred hiT hij
  have hcons := oddBelow_consec hjT hpj hgap
  have hOij : oddPts T i j = oddPts T i p + oddPts T p j := oddPts_trans T hip hpj.le
  have hpodd : OddBelow T p := by
    by_contra hnp
    have h0 : oddPts T p j = 0 :=
      oddPts_of_none fun z h1 h2 => fun hz => hnp (((hcons.1 z h1 h2).mp hz))
    rcases eq_or_lt_of_le hip with hpi | hpi
    · subst hpi
      have : oddPts T i i = 0 := by simp [oddPts]
      omega
    · have hpE : p ∈ T.erase i := Finset.mem_erase.mpr ⟨by omega, hpT⟩
      have hvp : ValidAnswer T e i p := (validAnswer_above_iff hev hiT hpE hpi).mpr (by omega)
      have := hjmin p hpE hvp
      omega
  have hOpj : oddPts T p j = j - p := oddPts_of_all fun z h1 h2 => (hcons.1 z h1 h2).mpr hpodd
  have hjtop : ¬ OddBelow T j := fun h => (hcons.2.mp h) hpodd
  -- (*) e ≤ c − 2 O(i, p) − 2.
  have hstar : (e : ℤ) ≤ matchCost T - 2 * oddPts T i p - 2 := by
    rcases eq_or_lt_of_le hip with hpi | hpi
    · subst hpi
      have : oddPts T i i = 0 := by simp [oddPts]
      rw [this]
      omega
    · have hpE : p ∈ T.erase i := Finset.mem_erase.mpr ⟨by omega, hpT⟩
      have hnv : ¬ ValidAnswer T e i p := fun hvp => by have := hjmin p hpE hvp; omega
      rw [validAnswer_above_iff hev hiT hpE hpi] at hnv
      omega
  -- (**) E(i, p) − O(i, p) ≤ η + [i a top].
  have hstar2 : (evenPts T i p : ℤ) - oddPts T i p ≤ eta T + (if OddBelow T i then 0 else 1) := by
    rcases eq_or_lt_of_le hip with hpi | hpi
    · subst hpi
      have h1 : oddPts T i i = 0 := by simp [oddPts]
      have h2 : evenPts T i i = 0 := by simp [evenPts]
      rw [h1, h2]
      split_ifs
      omega
    · have hE := evenPts_le_tops_add_eta (T := T) (x := i) (y := p) (lo_le hiT) (le_hi hpT)
      have hB := bottoms_le_oddPts T i p
      have hA := bottoms_sub_tops_Ico hiT hpT hpi
      simp only [hpodd, ↓reduceIte] at hA
      split_ifs at hA ⊢ <;> omega
  have hEpj : evenPts T p j = 0 := by have := oddPts_add_evenPts T p j; omega
  have hEij : evenPts T i j = evenPts T i p := by rw [evenPts_trans T hip hpj.le, hEpj]; simp
  have hOEip := oddPts_add_evenPts T i p
  have hOEij := oddPts_add_evenPts T i j
  -- The next start is Y's, after the switch.
  have hc1 := Finset.card_erase_add_one hiT
  have hc2 := Finset.card_erase_add_one hj
  have h2'' : 2 ≤ ((T.erase i).erase j).card := by omega
  have hcost'' :
      matchCost ((T.erase i).erase j) = matchCost T + ((j : ℤ) - i) - 2 * oddPts T i j := by
    rw [matchCost_erase_pair hev hiT hj, min_eq_left hij.le, max_eq_right hij.le,
      abs_of_nonneg (by omega)]
  have hpost : ¬ ((e + j - i : ℕ) : ℤ) < matchCost ((T.erase i).erase j) := by
    push_cast [hle]
    omega
  have hW : potW T e false = psi T := by simp [potW, hlost]
  have hW'' : potW ((T.erase i).erase j) (e + j - i) false =
      max (((e + j - i : ℕ) : ℤ) - lo ((T.erase i).erase j))
        (min (((e + j - i : ℕ) : ℤ) + matchCost ((T.erase i).erase j) -
          second ((T.erase i).erase j)) (psi ((T.erase i).erase j))) := by
    simp [potW, hpost]
  rw [hW, hW'', psi_eq hev (by omega)]
  have hsec := second_le_second_erase_two hiT hj h2''
  have hne'' : ((T.erase i).erase j).Nonempty := Finset.card_pos.mp (by omega)
  have hlo'' : lo T ≤ lo ((T.erase i).erase j) := lo_le_lo_of_subset
    (fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)) hne''
  have heta := Nat.zero_le (eta T)
  -- (f) the climb term X'' stays below Ψ(T).
  have hX : ((e + j - i : ℕ) : ℤ) - lo ((T.erase i).erase j) ≤
      2 * (matchCost T + eta T) - second T := by
    push_cast [hle]
    by_cases hplo : p = lo T
    · -- p is the least element, so i = p and j is the second smallest.
      have hilo : i = lo T := le_antisymm (by omega) (lo_le hiT)
      have hjsec : j = second T := by
        have h2 : 2 ≤ T.card := by omega
        have hs := second_mem h2
        have hsT := Finset.mem_of_mem_erase hs
        have hsne : second T ≠ lo T := Finset.ne_of_mem_erase hs
        have h1 := second_le hjT (by omega)
        by_contra hne
        exact hgap (second T) hsT ⟨by have := lo_le hsT; omega, by omega⟩
      have hloT2 : second T + 1 ≤ lo ((T.erase i).erase j) := by
        have hm := lo_mem hne''
        have hm1 := Finset.mem_erase.mp hm
        have hm2 := Finset.mem_erase.mp hm1.2
        have := second_le hm2.2 (by omega)
        omega
      have hc := oddPts_le_matchCost hev (x := p) (y := j) (by omega) hpj.le (le_hi hjT)
      split_ifs at hstar2 <;> omega
    · have hsp : second T ≤ p := second_le hpT hplo
      have h2 : 2 ≤ T.card := by omega
      have hlos : lo T ≤ second T := lo_le (Finset.mem_of_mem_erase (second_mem h2))
      have hjhi := le_hi hjT
      have hsum : (oddPts T (lo T) (second T) : ℤ) + oddPts T p j ≤ matchCost T := by
        rw [matchCost_eq_oddPts hev, oddPts_trans T hlos (hsp.trans (hpj.le.trans hjhi)),
          oddPts_trans T hsp (hpj.le.trans hjhi), oddPts_trans T hpj.le hjhi]
        push_cast
        omega
      have hls := oddPts_lo_second (T := T) h2
      split_ifs at hstar2 <;> omega
  -- (e) the debt-plus-cost term stays below Ψ(T).
  have hP : ((e + j - i : ℕ) : ℤ) + matchCost ((T.erase i).erase j) - second ((T.erase i).erase j) ≤
      2 * (matchCost T + eta T) - second T := by
    push_cast [hle]
    rw [hcost'']
    split_ifs at hstar2 <;> omega
  exact max_le hX ((min_le_left _ _).trans hP)

/-- The least element is a bottom. -/
theorem oddBelow_lo {T : Finset ℕ} (h : T.Nonempty) : OddBelow T (lo T) := by
  rw [oddBelow_iff_of_mem (lo_mem h)]
  have : below T (lo T) = 0 := by
    unfold below
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    have := lo_le hx
    omega
  omega

/-- Validity of an answer below Y's pick: twice the even points between is at most the slack. -/
theorem validAnswer_below_iff {T : Finset ℕ} (hev : Even T.card) {e i x : ℕ} (hiT : i ∈ T)
    (hx : x ∈ T.erase i) (hxi : x < i) :
    ValidAnswer T e i x ↔ 2 * (evenPts T x i : ℤ) ≤ e - matchCost T := by
  have hOE := oddPts_add_evenPts T x i
  rw [validAnswer_iff, matchCost_erase_pair hev hiT hx, min_eq_right hxi.le, max_eq_left hxi.le,
    abs_of_neg (by omega)]
  constructor <;> intro h <;> omega

/-- **T4.** Y moves after the switch (`c ≤ e`): Hyb2T's smallest valid answer keeps W. -/
theorem potW_y_round_post {T : Finset ℕ} (hev : Even T.card) (h4 : 4 ≤ T.card) {e i : ℕ}
    (hpar : (e + ∑ o ∈ T, o) % 2 = 0) (hiT : i ∈ T) (hpost : matchCost T ≤ e) :
    (i ≤ e + hyb2Reply T e i →
      potW ((T.erase i).erase (hyb2Reply T e i)) (e + hyb2Reply T e i - i) false ≤
        potW T e false) ∧
    (¬ i ≤ e + hyb2Reply T e i →
      potW ((T.erase i).erase (hyb2Reply T e i)) (i - e - hyb2Reply T e i) true ≤
        potW T e false) := by
  obtain ⟨j0, hj0, hv0⟩ := exists_valid_of_lost (e := e) hev hiT hpost
  obtain ⟨hj, hvj, -⟩ := hyb2Reply_min hj0 hv0
  set j := hyb2Reply T e i with hjdef
  have hjmin : ∀ x ∈ T.erase i, ValidAnswer T e i x → j ≤ x :=
    fun x hx hvx => (hyb2Reply_min hx hvx).2.2
  have hjT := Finset.mem_of_mem_erase hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  refine ⟨fun hle => ?_, fun hle => absurd hvj.1 hle⟩
  have hσ : ((e : ℤ) - matchCost T) % 2 = 0 := by
    have h1 := matchCost_parity hev
    have h2 : ((e + ∑ o ∈ T, o : ℕ) : ℤ) % 2 = 0 := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hpar
    push_cast at h2
    omega
  have hne : T.Nonempty := ⟨i, hiT⟩
  have h2 : 2 ≤ T.card := by omega
  have hc1 := Finset.card_erase_add_one hiT
  have hc2 := Finset.card_erase_add_one hj
  have h2'' : 2 ≤ ((T.erase i).erase j).card := by omega
  have hne'' : ((T.erase i).erase j).Nonempty := Finset.card_pos.mp (by omega)
  have hlo'' : lo T ≤ lo ((T.erase i).erase j) := lo_le_lo_of_subset
    (fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)) hne''
  have hsec := second_le_second_erase_two hiT hj h2''
  have hpsiT := psi_eq hev h2
  have heta := Nat.zero_le (eta T)
  have hlomem := lo_mem hne
  have hlobot := oddBelow_lo hne
  have hW : potW T e false = max ((e : ℤ) - lo T)
      (min ((e : ℤ) + matchCost T - second T) (psi T)) := by
    simp [potW, not_lt.mpr hpost]
  have hpost'' : ¬ ((e + j - i : ℕ) : ℤ) < matchCost ((T.erase i).erase j) := by
    have := validAnswer_iff.mp hvj
    push_cast [hle]
    omega
  have hW'' : potW ((T.erase i).erase j) (e + j - i) false = max (((e + j - i : ℕ) : ℤ) -
      lo ((T.erase i).erase j)) (min (((e + j - i : ℕ) : ℤ) + matchCost ((T.erase i).erase j) -
        second ((T.erase i).erase j)) (psi ((T.erase i).erase j))) := by
    simp [potW, hpost'']
  rw [hW, hW'']
  rcases lt_or_gt_of_ne hji with hjlt | hjgt
  · -- (Bt), (Bb): the answer is below the pick.
    have hcost'' : matchCost ((T.erase i).erase j) =
        matchCost T + ((i : ℤ) - j) - 2 * oddPts T j i := by
      rw [matchCost_erase_pair hev hiT hj, min_eq_right hjlt.le, max_eq_left hjlt.le,
        abs_of_neg (by omega)]
      ring
    have hX : ((e + j - i : ℕ) : ℤ) - lo ((T.erase i).erase j) ≤ (e : ℤ) - lo T := by
      push_cast [hle]
      omega
    have hOE := oddPts_add_evenPts T j i
    have hP2 : ((e + j - i : ℕ) : ℤ) + matchCost ((T.erase i).erase j) -
        second ((T.erase i).erase j) ≤ (e : ℤ) + matchCost T - second T - 2 * oddPts T j i := by
      push_cast [hle]
      rw [hcost'']
      omega
    refine max_le (hX.trans (le_max_left _ _)) ?_
    by_cases hlow : (e : ℤ) - matchCost T ≤ 2 * eta T
    · -- Low slack: min(Ψ₂, Ψ) = Ψ₂, and Ψ₂ does not rise.
      have hmin : min ((e : ℤ) + matchCost T - second T) (psi T) =
          (e : ℤ) + matchCost T - second T := min_eq_left (by rw [hpsiT]; omega)
      rw [hmin]
      exact (min_le_left _ _).trans (hP2.trans (by omega)) |>.trans (le_max_right _ _)
    · -- High slack: min(Ψ₂, Ψ) = Ψ.
      have hmin : min ((e : ℤ) + matchCost T - second T) (psi T) = psi T :=
        min_eq_right (by rw [hpsiT]; omega)
      rw [hmin]
      refine le_trans ?_ (le_max_right _ _)
      by_cases hjlo : j = lo T
      · exact (min_le_right _ _).trans (psi_erase_two_le hiT hj (by tauto) h2'')
      · refine (min_le_left _ _).trans (hP2.trans ?_)
        -- The element `q` just below `j`: a top, and not a valid answer.
        have hloj : lo T < j := lt_of_le_of_ne (lo_le hjT) (Ne.symm hjlo)
        obtain ⟨q, hqT, -, hqj, hgap⟩ := exists_pred hlomem hloj
        have hcons := oddBelow_consec hjT hqj hgap
        have hqE : q ∈ T.erase i := Finset.mem_erase.mpr ⟨by omega, hqT⟩
        have hqinv : ¬ ValidAnswer T e i q := fun hv => by have := hjmin q hqE hv; omega
        rw [validAnswer_below_iff hev hiT hqE (by omega)] at hqinv
        have hjbot : OddBelow T j := by
          by_contra hjt
          have hqb : OddBelow T q := by
            by_contra hq
            exact hjt (hcons.2.mpr hq)
          have hEqj : evenPts T q j = 0 := by
            have h0 := oddPts_of_all (T := T) (x := q) (y := j)
              fun z h1 h2 => (hcons.1 z h1 h2).mpr hqb
            have := oddPts_add_evenPts T q j
            omega
          have hvj' := (validAnswer_below_iff hev hiT hj hjlt).mp hvj
          have := evenPts_trans T hqj.le hjlt.le
          omega
        have hqtop : ¬ OddBelow T q := hcons.2.mp hjbot
        have hOqj : oddPts T q j = 0 :=
          oddPts_of_none fun z h1 h2 => fun hz => hqtop ((hcons.1 z h1 h2).mp hz)
        have hOqi := oddPts_trans T hqj.le hjlt.le
        have hE := evenPts_le_tops_add_eta (T := T) (x := q) (y := i) (lo_le hqT) (le_hi hiT)
        have hB := bottoms_le_oddPts T q i
        have hA := bottoms_sub_tops_Ico hqT hiT (by omega)
        simp only [hqtop, ↓reduceIte] at hA
        rw [hpsiT]
        split_ifs at hA <;> omega
  · -- (C): the answer is above the pick, so `i` is a bottom and `j` its successor.
    have hgap : ∀ x ∈ T, ¬ (i < x ∧ x < j) := by
      rintro x hx ⟨h1, h2⟩
      have hxE : x ∈ T.erase i := Finset.mem_erase.mpr ⟨by omega, hx⟩
      have hbound := oddPts_le_matchCost hev (x := i) (y := x) (lo_le hiT) h1.le (le_hi hx)
      have hvx : ValidAnswer T e i x :=
        (validAnswer_above_iff hev hiT hxE h1).mpr (by omega)
      have := hjmin x hxE hvx
      omega
    have hcons := oddBelow_consec hjT hjgt hgap
    have hnobelow : ∀ x ∈ T.erase i, x < i → ¬ ValidAnswer T e i x :=
      fun x hx hxi hv => by have := hjmin x hx hv; omega
    have hibot : OddBelow T i := by
      by_contra hit
      have hilo : lo T < i := lt_of_le_of_ne (lo_le hiT) (fun h => hit (h ▸ hlobot))
      obtain ⟨q, hqT, -, hqi, hgapq⟩ := exists_pred hlomem hilo
      have hconsq := oddBelow_consec hiT hqi hgapq
      have hqb : OddBelow T q := by
        by_contra hq
        exact hit (hconsq.2.mpr hq)
      have hEqi : evenPts T q i = 0 := by
        have h0 := oddPts_of_all (T := T) (x := q) (y := i)
          fun z h1 h2 => (hconsq.1 z h1 h2).mpr hqb
        have := oddPts_add_evenPts T q i
        omega
      have hqE : q ∈ T.erase i := Finset.mem_erase.mpr ⟨by omega, hqT⟩
      exact hnobelow q hqE hqi ((validAnswer_below_iff hev hiT hqE hqi).mpr (by omega))
    have hOij : oddPts T i j = j - i := oddPts_of_all fun z h1 h2 => (hcons.1 z h1 h2).mpr hibot
    have hcost'' : matchCost ((T.erase i).erase j) = matchCost T - ((j : ℤ) - i) := by
      rw [matchCost_erase_pair hev hiT hj, min_eq_left hjgt.le, max_eq_right hjgt.le,
        abs_of_nonneg (by omega), hOij]
      push_cast [hjgt.le]
      ring
    have hP2 : ((e + j - i : ℕ) : ℤ) + matchCost ((T.erase i).erase j) -
        second ((T.erase i).erase j) ≤ (e : ℤ) + matchCost T - second T := by
      push_cast [hle]
      rw [hcost'']
      omega
    by_cases hilo : i = lo T
    · -- Y took the least element: X falls and Ψ does not rise.
      have hjsec : j = second T := by
        have hs := second_mem h2
        have hsT := Finset.mem_of_mem_erase hs
        have h1 := second_le hjT (by omega)
        by_contra hne'
        have h3 := Finset.ne_of_mem_erase hs
        have h4 := lo_le hsT
        exact hgap (second T) hsT ⟨by omega, by omega⟩
      have hloT2 : second T + 1 ≤ lo ((T.erase i).erase j) := by
        have hm := lo_mem hne''
        have hm1 := Finset.mem_erase.mp hm
        have hm2 := Finset.mem_erase.mp hm1.2
        have := second_le hm2.2 (by omega)
        omega
      have hX : ((e + j - i : ℕ) : ℤ) - lo ((T.erase i).erase j) ≤ (e : ℤ) - lo T := by
        push_cast [hle]
        omega
      have hpsi'' := psi_erase_two_le hiT hj (Or.inl hilo) h2''
      exact max_le_max hX (min_le_min hP2 hpsi'')
    · -- A climb above the least element: the slack is low, so W = max(X, Ψ₂) and X + g ≤ Ψ₂.
      have hloi : lo T < i := lt_of_le_of_ne (lo_le hiT) (Ne.symm hilo)
      obtain ⟨q, hqT, -, hqi, hgapq⟩ := exists_pred hlomem hloi
      have hconsq := oddBelow_consec hiT hqi hgapq
      have hqtop : ¬ OddBelow T q := hconsq.2.mp hibot
      have hqE : q ∈ T.erase i := Finset.mem_erase.mpr ⟨by omega, hqT⟩
      have hqinv := hnobelow q hqE hqi
      rw [validAnswer_below_iff hev hiT hqE hqi] at hqinv
      have hOqi : oddPts T q i = 0 :=
        oddPts_of_none fun z h1 h2 => fun hz => hqtop ((hconsq.1 z h1 h2).mp hz)
      have hE := evenPts_le_tops_add_eta (T := T) (x := q) (y := i) (lo_le hqT) (le_hi hiT)
      have hB := bottoms_le_oddPts T q i
      have hA := bottoms_sub_tops_Ico hqT hiT hqi
      simp only [hqtop, hibot, ↓reduceIte] at hA
      have hlow : (e : ℤ) - matchCost T ≤ 2 * eta T := by omega
      have hmin : min ((e : ℤ) + matchCost T - second T) (psi T) =
          (e : ℤ) + matchCost T - second T := min_eq_left (by rw [hpsiT]; omega)
      rw [hmin]
      have hloT : lo ((T.erase i).erase j) = lo T := by
        apply le_antisymm _ hlo''
        apply lo_le
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨hilo ∘ Eq.symm, hlomem⟩⟩
        intro h
        have := lo_le hiT
        omega
      have hsi : second T ≤ i := second_le hiT hilo
      have hjhi := le_hi hjT
      have hlos : lo T ≤ second T := lo_le (Finset.mem_of_mem_erase (second_mem h2))
      have hsum : (oddPts T (lo T) (second T) : ℤ) + oddPts T i j ≤ matchCost T := by
        rw [matchCost_eq_oddPts hev, oddPts_trans T hlos (hsi.trans (hjgt.le.trans hjhi)),
          oddPts_trans T hsi (hjgt.le.trans hjhi), oddPts_trans T hjgt.le hjhi]
        push_cast
        omega
      have hls := oddPts_lo_second (T := T) h2
      refine max_le ?_ ((min_le_left _ _).trans (hP2.trans (le_max_right _ _)))
      refine le_trans ?_ (le_max_right _ _)
      rw [hloT]
      push_cast [hle]
      omega

/-- **T2–T4, L25's claim for Y's rounds.** Y picks `i`, Z answers Hyb2T; W does not rise (parity
(C2) assumed). -/
theorem potW_y_round {T : Finset ℕ} (hev : Even T.card) (h4 : 4 ≤ T.card) {e i : ℕ}
    (hpar : (e + ∑ o ∈ T, o) % 2 = 0) (hiT : i ∈ T) :
    (i ≤ e + hyb2Reply T e i →
      potW ((T.erase i).erase (hyb2Reply T e i)) (e + hyb2Reply T e i - i) false ≤
        potW T e false) ∧
    (¬ i ≤ e + hyb2Reply T e i →
      potW ((T.erase i).erase (hyb2Reply T e i)) (i - e - hyb2Reply T e i) true ≤
        potW T e false) := by
  by_cases hpost : matchCost T ≤ e
  · exact potW_y_round_post hev h4 hpar hiT hpost
  · by_cases hval : ∃ j ∈ T.erase i, ValidAnswer T e i j
    · obtain ⟨j0, hj0, hv0⟩ := hval
      exact potW_y_round_switch hev h4 hpar hiT (by omega) hj0 hv0
    · push Not at hval
      exact potW_y_round_fallback hev h4 hiT hval

/-! ## L24: blocks at the doubling-free height -/

open Classical in
/-- Hyb2T's answer when no answer is valid is AM+T's. -/
theorem hyb2Reply_eq_amtReply {T : Finset ℕ} {e i : ℕ}
    (hnone : ∀ j ∈ T.erase i, ¬ ValidAnswer T e i j) :
    hyb2Reply T e i = amtReply (T.erase i) e i := by
  have hne : ¬ ((T.erase i).filter (ValidAnswer T e i)).Nonempty := by
    rintro ⟨j, hj⟩
    exact hnone j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  unfold hyb2Reply
  simp only [hne, ↓reduceDIte]

/-- Z's round starts on a block: L23's class, debt at most `2p − 1`, and W at most `2p − 1`. -/
def HZw (p : ℕ) (T : Finset ℕ) (d : ℕ) : Prop :=
  T ⊆ Finset.range (2 * p) ∧ Even T.card ∧ (d + ∑ o ∈ T, o) % 2 = 0 ∧ KZc T d ∧ d ≤ 2 * p - 1 ∧
    (2 ≤ T.card → potW T d true ≤ 2 * p - 1)

/-- Y's round starts on a block: before the switch in L23's class, or after it; W at most
`2p − 1`. -/
def HYw (p : ℕ) (T : Finset ℕ) (e : ℕ) : Prop :=
  T ⊆ Finset.range (2 * p) ∧ Even T.card ∧ (e + ∑ o ∈ T, o) % 2 = 0 ∧
    (((e : ℤ) < matchCost T ∧ KYc T e) ∨ matchCost T ≤ e) ∧
    (2 ≤ T.card → potW T e false ≤ 2 * p - 1)

private theorem round_facts_w {T : Finset ℕ} (hev : Even T.card) {a b : ℕ} (ha : a ∈ T)
    (hb : b ∈ T.erase a) :
    Even ((T.erase a).erase b).card ∧ ∑ o ∈ (T.erase a).erase b, o + b + a = ∑ o ∈ T, o ∧
      (T.erase a).erase b ⊆ T ∧ ((T.erase a).erase b).card + 2 = T.card := by
  have h1 := Finset.card_erase_add_one ha
  have h2 := Finset.card_erase_add_one hb
  have hs1 := Finset.sum_erase_add T (fun o => o) ha
  have hs2 := Finset.sum_erase_add (T.erase a) (fun o => o) hb
  obtain ⟨k, hk⟩ := hev
  exact ⟨⟨k - 1, by omega⟩, by omega,
    fun x hx => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx), by omega⟩

theorem hz_step_w {p : ℕ} {T : Finset ℕ} {d : ℕ} (hK : HZw p T d) (h : T.Nonempty) :
    ∀ j ∈ T.erase (hi T),
      (hi T ≤ d + j → HZw p ((T.erase (hi T)).erase j) (d + j - hi T)) ∧
      (¬ hi T ≤ d + j → HYw p ((T.erase (hi T)).erase j) (hi T - d - j)) := by
  intro j hj
  obtain ⟨hsub, hev, hpar, hKZ, hd, hW⟩ := hK
  have hm := hi_mem h
  obtain ⟨hev2, hsum, hsub2, hcard⟩ := round_facts_w hev hm hj
  have hmax : T.max' h = hi T := (hi_of_nonempty h).symm
  have hj' : j ∈ T.erase (T.max' h) := hmax ▸ hj
  obtain ⟨hc1, hc2⟩ := closeZ hev h hKZ hj'
  rw [hmax] at hc1 hc2
  have hjlt : j < hi T := lt_of_le_of_ne (le_hi (Finset.mem_of_mem_erase hj))
    (Finset.ne_of_mem_erase hj)
  have hWz : 2 ≤ ((T.erase (hi T)).erase j).card → 4 ≤ T.card := fun h2 => by omega
  refine ⟨fun hc => ⟨hsub2.trans hsub, hev2, by omega, hc1 hc, by omega, fun h2 =>
      ((potW_z_round (hWz h2) hj).1 hc).trans (hW (by omega))⟩,
    fun hc => ⟨hsub2.trans hsub, hev2, by omega, ?_, fun h2 =>
      ((potW_z_round (hWz h2) hj).2 hc).trans (hW (by omega))⟩⟩
  by_cases hlt : ((hi T - d - j : ℕ) : ℤ) < matchCost ((T.erase (hi T)).erase j)
  · exact Or.inl ⟨hlt, hc2 hc⟩
  · exact Or.inr (by omega)

theorem hy_step_w {p : ℕ} {T : Finset ℕ} {e : ℕ} (hK : HYw p T e) :
    ∀ i ∈ T, ∃ j ∈ T.erase i,
      (i ≤ e + j → HYw p ((T.erase i).erase j) (e + j - i)) ∧
      (¬ i ≤ e + j → HZw p ((T.erase i).erase j) (i - e - j)) := by
  intro i hiT
  obtain ⟨hsub, hev, hpar, hcase, hW⟩ := hK
  have hiR := Finset.mem_range.mp (hsub hiT)
  -- Hyb2T's answer and W's bound for the next start.
  have hstep : ∀ j ∈ T.erase i, j = hyb2Reply T e i →
      (i ≤ e + j → 2 ≤ ((T.erase i).erase j).card →
        potW ((T.erase i).erase j) (e + j - i) false ≤ 2 * p - 1) ∧
      (¬ i ≤ e + j → 2 ≤ ((T.erase i).erase j).card →
        potW ((T.erase i).erase j) (i - e - j) true ≤ 2 * p - 1) := by
    rintro j hj rfl
    obtain ⟨-, -, -, hcard⟩ := round_facts_w hev hiT hj
    refine ⟨fun hc h2 => ?_, fun hc h2 => ?_⟩
    · exact ((potW_y_round hev (by omega) hpar hiT).1 hc).trans (hW (by omega))
    · exact ((potW_y_round hev (by omega) hpar hiT).2 hc).trans (hW (by omega))
  by_cases hval : ∃ j ∈ T.erase i, ValidAnswer T e i j
  · -- A valid answer: the next start is Y's, after the switch.
    obtain ⟨j0, hj0, hv0⟩ := hval
    obtain ⟨hj, hvj, -⟩ := hyb2Reply_min hj0 hv0
    refine ⟨hyb2Reply T e i, hj, fun hc => ?_, fun hc => absurd hvj.1 hc⟩
    obtain ⟨hev2, hsum, hsub2, -⟩ := round_facts_w hev hiT hj
    have hv := validAnswer_iff.mp hvj
    refine ⟨hsub2.trans hsub, hev2, by omega, Or.inr ?_, (hstep _ hj rfl).1 hc⟩
    push_cast [hc]
    linarith
  · -- No valid answer: Y was before the switch, and Hyb2T answers AM+T.
    push Not at hval
    have hpre : (e : ℤ) < matchCost T ∧ KYc T e := by
      rcases hcase with h | h
      · exact h
      · obtain ⟨j', hj', hv'⟩ := exists_valid_of_lost (e := e) hev hiT h
        exact absurd hv' (hval j' hj')
    have hamt := hyb2Reply_eq_amtReply hval
    have hj := (hyb2Reply_fallback hev hiT hval).1
    refine ⟨hyb2Reply T e i, hj, fun hc => ?_, fun hc => ?_⟩
    · obtain ⟨hev2, hsum, hsub2, -⟩ := round_facts_w hev hiT hj
      have hKY := (closeY hev hpre.2 hiT).1 (by rw [← hamt]; exact hc)
      rw [← hamt] at hKY
      refine ⟨hsub2.trans hsub, hev2, by omega, ?_, (hstep _ hj rfl).1 hc⟩
      by_cases hlt : ((e + hyb2Reply T e i - i : ℕ) : ℤ) <
          matchCost ((T.erase i).erase (hyb2Reply T e i))
      · exact Or.inl ⟨hlt, hKY⟩
      · exact Or.inr (by omega)
    · obtain ⟨hev2, hsum, hsub2, -⟩ := round_facts_w hev hiT hj
      have hKZ := (closeY hev hpre.2 hiT).2 (by rw [← hamt]; exact hc)
      rw [← hamt] at hKZ
      exact ⟨hsub2.trans hsub, hev2, by omega, hKZ, by omega, (hstep _ hj rfl).2 hc⟩

theorem psi_range {p : ℕ} (hp : 1 ≤ p) : psi (Finset.range (2 * p)) = 2 * p - 1 := by
  have hne : (Finset.range (2 * p)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hlo : lo (Finset.range (2 * p)) = 0 :=
    Nat.le_zero.mp (lo_le (Finset.mem_range.mpr (by omega)))
  have hhi : hi (Finset.range (2 * p)) = 2 * p - 1 := by
    apply le_antisymm
    · have := Finset.mem_range.mp (hi_mem hne); omega
    · exact le_hi (Finset.mem_range.mpr (by omega))
  have hsec : second (Finset.range (2 * p)) = 1 := by
    have h2 : 2 ≤ (Finset.range (2 * p)).card := by rw [Finset.card_range]; omega
    have hs := second_mem h2
    have hne' : second (Finset.range (2 * p)) ≠ 0 := by
      have := Finset.ne_of_mem_erase hs; rwa [hlo] at this
    have hle : second (Finset.range (2 * p)) ≤ 1 :=
      second_le (Finset.mem_range.mpr (by omega)) (by rw [hlo]; omega)
    omega
  unfold psi
  rw [hlo, hhi, hsec, Finset.card_range]
  push_cast [show 1 ≤ 2 * p by omega]
  ring

/-- **L24 rows, Lean form.** The block `{a, …, a + 2p − 1}` with `a ≥ 2p − 1` is a draw for the
player to move trailing by any `d ≤ p` with `d ≡ p (mod 2)`. -/
theorem block_row_draw_hyb2 {p a d : ℕ} (hp : 1 ≤ p) (ha : 2 * p - 1 ≤ a) (hd : d ≤ p)
    (hdp : d % 2 = p % 2) (s : ℕ) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + d) false = .draw := by
  have hT := valueAux_transfer a (HZw p) (HYw p)
    (fun T d hK o ho => by
      have := Finset.mem_range.mp (hK.1 ho); have := hK.2.2.2.2.1; omega)
    (fun T e hK o ho => by
      have hoR := Finset.mem_range.mp (hK.1 ho)
      refine ⟨by omega, ?_⟩
      rcases hK.2.2.2.1 with ⟨he, -⟩ | he
      · have := matchCost_le_range hp hK.1; omega
      · have hcard : 2 ≤ T.card := by
          obtain ⟨k, hk⟩ := hK.2.1
          have : 0 < T.card := Finset.card_pos.mpr ⟨o, ho⟩
          omega
        have hW := hK.2.2.2.2 hcard
        have hlo := lo_le ho
        simp only [potW, Bool.false_eq_true, false_or, not_lt.mpr he, ↓reduceIte] at hW
        have := le_max_left ((e : ℤ) - lo T) (min ((e : ℤ) + matchCost T - second T) (psi T))
        omega)
    (fun d hK => by
      have h1 := hK.2.2.2.1.1 (by simp)
      have h2 := hK.2.2.1
      simp at h2
      omega)
    (fun T d hK h => ⟨hi T, hi_mem h, hz_step_w hK h⟩)
    (fun T e hK => hy_step_w hK)
    (2 * p) (Finset.range (2 * p)) (Finset.card_range _)
  have hev : Even (Finset.range (2 * p)).card := by rw [Finset.card_range]; exact even_two_mul p
  have hpar : (d + ∑ o ∈ Finset.range (2 * p), o) % 2 = 0 := by
    rw [sum_range_two_mul, Nat.add_mod, Nat.mul_mod]
    have : (2 * p - 1) % 2 = 1 := by omega
    rw [this, mul_one, Nat.mod_mod]
    omega
  have hcost := matchCost_le_range hp (subset_refl (Finset.range (2 * p)))
  have hpsi := psi_range hp
  have hZ : HZw p (Finset.range (2 * p)) d :=
    ⟨subset_refl _, hev, hpar, kzc_range hp hd, by omega, fun _ => by
      simp only [potW, true_or, ↓reduceIte]; exact hpsi.le⟩
  have hYw : HYw p (Finset.range (2 * p)) d := by
    refine ⟨subset_refl _, hev, hpar, ?_, fun _ => ?_⟩
    · by_cases hlt : (d : ℤ) < matchCost (Finset.range (2 * p))
      · exact Or.inl ⟨hlt, kyc_range p d⟩
      · exact Or.inr (by omega)
    · by_cases hlt : (d : ℤ) < matchCost (Finset.range (2 * p))
      · simp only [potW, Bool.false_eq_true, false_or, hlt, ↓reduceIte]
        exact hpsi.le
      · simp only [potW, Bool.false_eq_true, false_or, hlt, ↓reduceIte]
        rw [hpsi]
        refine max_le ?_ (min_le_right _ _)
        have := Nat.zero_le (lo (Finset.range (2 * p)))
        omega
  have hZ' := hT.1 d hZ s
  have hY' := hT.2 d hYw s
  revert hZ' hY'
  cases valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + d) false <;> simp

/-- **L24, Lean form.** The block `{a, …, a + 2p − 1}` with `a ≥ 2p − 1` is a draw for the player
to move trailing by `p mod 2`, from any common base score `s`. -/
theorem block_draw_hyb2 {p a : ℕ} (hp : 1 ≤ p) (ha : 2 * p - 1 ≤ a) (s : ℕ) :
    valueAux ((Finset.range (2 * p)).map (addLeftEmbedding a)) s (s + p % 2) false = .draw :=
  block_row_draw_hyb2 hp ha (by omega) (Nat.mod_mod p 2) s

end CatchUp

