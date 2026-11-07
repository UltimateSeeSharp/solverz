module

public import SignedDifferenceSets.LiftSearch

/-!
# Tests: contraction, then lift

The checks must not kill sets that exist: (9, 8, −1) in C₃² (both coset-sum vectors on C₃ lift),
N73 (27, 17, 8) in C₃³ and N137 (32, 28, 12) in C₂ × C₄ × C₄ (a vector of each lifts). Phase 1
must list every vector, and `mapOK` must reject a coset-fixing bijection that is not affine.
-/

@[expose] public section

namespace SignedDifferenceSets.LiftSearch

/-- The coset-fixing affine maps of C₃² over its first factor, but the identity. -/
def t9Maps : List (List ℕ) :=
  [[0, 1, 2, 4, 5, 3, 8, 6, 7], [0, 1, 2, 5, 3, 4, 7, 8, 6], [1, 2, 0, 4, 5, 3, 7, 8, 6],
    [1, 2, 0, 5, 3, 4, 6, 7, 8], [1, 2, 0, 3, 4, 5, 8, 6, 7], [2, 0, 1, 5, 3, 4, 8, 6, 7],
    [2, 0, 1, 3, 4, 5, 7, 8, 6], [2, 0, 1, 4, 5, 3, 6, 7, 8]]

example : coverRow [3, 1] 3 8 (-1) 0 [[-2, 1, 1], [2, -1, -1]] = true := by decide +kernel

example : coverRow [3, 1] 3 8 (-1) 0 [[-2, 1, 1]] = false := by decide +kernel

example : mapsRow [3, 3] [3, 1] t9Maps = true := by decide +kernel

example : mapsRow [3, 3] [3, 1] [[0, 2, 1, 3, 4, 5, 6, 7, 8]] = false := by decide +kernel

example : liftRow [3, 3] [3, 1] [-2, 1, 1] [0, 1, 2] t9Maps 3 8 (-1) = false := by
  decide +kernel

example : liftRow [3, 3] [3, 1] [2, -1, -1] [0, 1, 2] t9Maps 3 8 (-1) = false := by
  decide +kernel

example : liftRow [3, 3, 3] [3, 3, 1] [3, 0, 0, 2, 2, 2, 2, 2, 2] [0, 3, 4, 5, 6, 7, 8, 1, 2] []
    0 17 8 = false := by
  decide +kernel

example : liftRow [2, 4, 4] [2, 2, 2] [4, 0, 2, 2, 2, 2, 4, 4] [0, 6, 7, 2, 3, 4, 5, 1] [] 0 28
    12 = false := by
  decide +kernel

end SignedDifferenceSets.LiftSearch
