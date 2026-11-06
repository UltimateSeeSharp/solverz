module

public import SignedDifferenceSets.CosetSearch

/-!
# Tests of the coset search (A7)

Kills from the A7 run closed through C16, the split into slices, and controls: on rows with a
known SDS the search must fail, on the group itself and on a proper quotient.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.CosetSearch

/-! ### Kills -/

/-- N7507, (177, 64, 7) in C₁₇₇, `n = 57`: on C₅₉ (`c = 3`) the cycles of `x ↦ 3x` are three
classes and no value on them meets C3. -/
example : ¬ HasSDS (ZMod 177) 64 7 :=
  not_hasSDS_of_cosetRow (ms := [177]) (ds := [59]) (c := 3) (t := 3) (s := 36)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _

/-- N2007, (99, 98, 1) in C₃ × C₃₃, `n = 97`: on C₁ × C₁₁ (`c = 9`) with `x ↦ 9x`. -/
example : ¬ HasSDS (ZMod 3 × ZMod 33) 98 1 :=
  not_hasSDS_of_cosetRow (ms := [3, 33]) (ds := [1, 11]) (c := 9) (t := 9) (s := 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _

/-! ### The split: N2007's search one level down has 6 nodes, checked in two slices -/

theorem n2007_slice0 : cosetSlice [1, 11] 9 98 1 9 14 1 0 4 = true := by decide +kernel

theorem n2007_slice1 : cosetSlice [1, 11] 9 98 1 9 14 1 4 6 = true := by decide +kernel

example : cosetSearch [1, 11] 9 98 1 9 14 = true :=
  cosetSearch_of_slices (d := 1) [4, 6] (by decide +kernel)
    (.cons n2007_slice0 (.cons n2007_slice1 .single))

/-- The top rejects a bound below the node count, so slices cannot skip nodes. -/
example : cosetTop [1, 11] 9 98 1 9 14 1 5 = false := by decide +kernel

/-! ### Controls: rows with a known SDS -/

-- N6 exists ((11, 6, 1), Paley and zero): on C₁₁ itself (`c = 1`) with `x ↦ 5x`, `s = 4`.
example : cosetSearch [11] 1 6 1 5 4 = false := by decide +kernel

-- N24 exists ((19, 10, 3), Paley and zero): `x ↦ 7x`, `s = 8`.
example : cosetSearch [19] 1 10 3 7 8 = false := by decide +kernel

-- N1640 exists ((91, 76, 60) in C₉₁, `n = 16`): its coset sums on C₁₃ (`c = 7`) are fixed by
-- `x ↦ 2x`, so the search on that quotient must fail; `s = 74`.
example : cosetSearch [13] 7 76 60 2 74 = false := by decide +kernel

/-! ### Row hypotheses -/

example : CosetRow [3, 33] [1, 11] 9 98 1 9 14 := by decide +kernel

-- `t` must act as a power of each prime of `n`: `x ↦ 2x` on C₁₁ is not a power of 97.
example : ¬ CosetRow [3, 33] [1, 11] 9 98 1 2 14 := by decide +kernel

-- The fibres must have `c` elements.
example : ¬ CosetRow [3, 33] [1, 11] 3 98 1 9 14 := by decide +kernel

example : SquarefreeTD 57 ∧ ¬ SquarefreeTD 16 := by decide +kernel

end SignedDifferenceSets.Tests.CosetSearch
