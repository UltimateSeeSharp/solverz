import SignedDifferenceSets.Square
import SignedDifferenceSets.Parity
import SignedDifferenceSets.Rows
import SignedDifferenceSets.Iso
import SignedDifferenceSets.Tests.Statement

/-! Refuter's attacks on Square, Parity, Rows, Iso. -/

set_option autoImplicit false

namespace C1C8Refuter
open SignedDifferenceSets

#print axioms IsSDS.sum_sq
#print axioms HasSDS.isSquare
#print axioms not_hasSDS_of_not_isSquare
#print axioms IsSDS.card_zeros
#print axioms IsSDS.exists_zeros_of_parity
#print axioms not_hasSDS_of_supportParity
#print axioms Grp.card_eq
#print axioms Grp.natCard_eq
#print axioms Grp.nsmul_eq_zero
#print axioms Grp.exists_ne_zero
#print axioms quot_surjective
#print axioms IsSDS.comp_addEquiv
#print axioms HasSDS.of_addEquiv
#print axioms hasSDS_congr
#print axioms hasSDS_congr_fintype

#check @not_hasSDS_of_supportParity
#check @not_hasSDS_of_not_isSquare
#check @Grp.card_eq

/-! C1: non-vacuous, implies the weighing-matrix corollary. -/
example : ¬ HasSDS (ZMod 5) 3 0 := not_hasSDS_of_not_isSquare (by
  rw [ZMod.card]; rintro ⟨r, hr⟩
  have h1 : r * r = 3 := by push_cast at hr; linarith
  have h2 : r ≤ 2 := by nlinarith
  have h3 : -2 ≤ r := by nlinarith
  interval_cases r <;> omega)
example {G : Type} [AddCommGroup G] [Fintype G] (k : ℕ) (h : HasSDS G k 0) :
    IsSquare (k : ℤ) := by simpa using h.isSquare
example : (∑ x : ZMod 7, (Tests.cw74 x : ℤ)) ^ 2 = 4 := by
  have := (show IsSDS 4 0 Tests.cw74 by decide).sum_sq; rw [this]; simp

/-! C8 edge cases. -/
example : SupportParity 3 4 0 := by decide            -- k > v: fires, and is true
example : ¬ HasSDS (ZMod 3) 4 0 := not_hasSDS_of_supportParity (ZMod.card 3) (by decide)
example : ¬ SupportParity 1 0 0 ∧ ¬ SupportParity 1 1 0 ∧ ¬ SupportParity 1 5 2 := by decide
example : HasSDS (ZMod 1) 0 0 := ⟨fun _ => 0, by decide⟩
example : HasSDS (ZMod 1) 1 2 := ⟨fun _ => 1, by decide⟩
example : SupportParity 5 4 (-2) ∧ SupportParity 7 7 0 ∧ ¬ SupportParity 9 8 1 := by decide
example : ¬ SupportParity 7 4 0 ∧ ¬ SupportParity 13 9 0 ∧ SupportParity 13 10 0 := by decide
example : HasSDS (ZMod 7) 4 0 ∧ ¬ SupportParity 7 4 0 := ⟨⟨Tests.cw74, by decide⟩, by decide⟩
example : ¬ SupportParity 8 7 0 ∧ ¬ SupportParity 0 0 0 := by decide

/-- He–Wu Cor 4.5 (d = 1) follows: v odd ≥ 3, λ even, k = v − 1 ⇒ no SDS. -/
example {G : Type} [AddCommGroup G] [Fintype G] (hv : Odd (Fintype.card G))
    (h3 : 3 ≤ Fintype.card G) (lam : ℤ) (hl : Even lam) :
    ¬ HasSDS G (Fintype.card G - 1) lam := by
  refine not_hasSDS_of_supportParity rfl ⟨hv, hl, ?_⟩
  have : Fintype.card G - (Fintype.card G - 1) = 1 := by omega
  rw [this]; omega

/-- Odd-order weighing matrix bound (λ = 0): v odd, W(v, k) circulant ⇒ (v−k)(v−k−1) ≥ v − 1. -/
example {G : Type} [AddCommGroup G] [Fintype G] (hv : Odd (Fintype.card G)) (k : ℕ)
    (h : HasSDS G k 0) :
    Fintype.card G - 1 ≤ (Fintype.card G - k) * (Fintype.card G - k - 1) := by
  by_contra hc
  exact not_hasSDS_of_supportParity rfl ⟨hv, by decide, by omega⟩ h

/-! Rows: the row form is the row's own group, for 0, 1, 2, 3, 5 factors and factor 1. -/
example (h : ∀ inst : Fintype (Grp []), ¬ @HasSDS (Grp []) _ inst 0 0) :
    ¬ HasSDS (ZMod 1) 0 0 := h _
example (h : ∀ inst : Fintype (Grp [1, 14]), ¬ @HasSDS (Grp [1, 14]) _ inst 13 4) :
    ¬ HasSDS (ZMod 1 × ZMod 14) 13 4 := h _
example (h : ∀ inst : Fintype (Grp [14, 1]), ¬ @HasSDS (Grp [14, 1]) _ inst 13 4) :
    ¬ HasSDS (ZMod 14 × ZMod 1) 13 4 := h _
example (h : ∀ inst : Fintype (Grp [2, 2, 2, 2, 2]), ¬ @HasSDS (Grp [2, 2, 2, 2, 2]) _ inst 20 4) :
    ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) 20 4 := h _
example : Grp.instAddCommGroup [2, 2, 8] = (inferInstance : AddCommGroup (ZMod 2 × ZMod 2 × ZMod 8)) :=
  rfl
example : Grp.instAddCommGroup [1, 14] = (inferInstance : AddCommGroup (ZMod 1 × ZMod 14)) := rfl
example : Grp.instAddCommGroup [49] = (inferInstance : AddCommGroup (ZMod 49)) := rfl
example : Grp.instAddCommGroup [] = (inferInstance : AddCommGroup (ZMod 1)) := rfl
example : ((((1 : ZMod 2), (7 : ZMod 10)) : Grp [2, 10]) + (((1 : ZMod 2), (5 : ZMod 10)) : Grp [2, 10]))
    = ((0 : ZMod 2), (2 : ZMod 10)) := by decide
example : Fintype.card (ZMod 1 × ZMod 14) = 14 := Grp.card_eq [1, 14]
example : Fintype.card (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) = 32 := Grp.card_eq [2, 2, 2, 2, 2]
example : Fintype.card (ZMod 1) = 1 := Grp.card_eq []
example : quot [2, 14] [1, 14] (by decide) ((1 : ZMod 2), (17 : ZMod 14)) =
    ((0 : ZMod 1), (3 : ZMod 14)) := by decide
example : quot [3, 9, 27] [3, 3, 9] (by decide) ((2 : ZMod 3), (8 : ZMod 9), (26 : ZMod 27)) =
    ((2 : ZMod 3), (2 : ZMod 3), (8 : ZMod 9)) := by decide
example : ∃ x : Grp [1, 1, 2], x ≠ 0 := Grp.exists_ne_zero _ (by decide)
example : ∀ x : Grp [1, 1], x = 0 := by decide
example (x : Grp [1, 14]) : 14 • x = 0 := Grp.nsmul_eq_zero [1, 14] (by decide) x
example : ∃ x : Grp [1, 14], 7 • x ≠ 0 := ⟨((0 : ZMod 1), (1 : ZMod 14)), by decide⟩
/-- A row with a factor 0 has no `Fintype` instance, so a row-form statement there is vacuous. -/
example (inst : Fintype (Grp [0, 3])) : False := by
  have h := @Grp.card_eq [0, 3] inst
  have : 0 < @Fintype.card (Grp [0, 3]) inst := @Fintype.card_pos _ inst ⟨0⟩
  simp at h

/-! Iso. -/
example (k : ℕ) (lam : ℤ) : HasSDS (ZMod 6) k lam ↔ HasSDS (ZMod 2 × ZMod 3) k lam :=
  hasSDS_congr (ZMod.chineseRemainder (m := 2) (n := 3) (by decide)).toAddEquiv
example : HasSDS (ZMod 2 × ZMod 3) 1 0 :=
  (hasSDS_congr (ZMod.chineseRemainder (m := 2) (n := 3) (by decide)).toAddEquiv).1
    ⟨fun x => if x = 0 then 1 else 0, by decide⟩

end C1C8Refuter
