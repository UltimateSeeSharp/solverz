import SignedDifferenceSets.Pds

open SignedDifferenceSets

/-! Refuter tests for C11's Lean statement (Pds.lean). -/

-- Positive: H \ {0} for H = {0,2,4,6} ≤ ZMod 8 is a PDS with λ' = 2, μ = 0.
theorem t1 : IsPDS ({2, 4, 6} : Finset (ZMod 8)) 2 0 := by unfold IsPDS; decide
example : HasSDS (ZMod 8) 4 0 := t1.hasSDS rfl
-- Negative controls: wrong λ', not symmetric, contains 0, non-PDS.
example : ¬ IsPDS ({2, 4, 6} : Finset (ZMod 8)) 1 0 := by unfold IsPDS; decide
example : ¬ IsPDS ({1, 2, 7} : Finset (ZMod 8)) 2 0 := by unfold IsPDS; decide
example : ¬ IsPDS ({0, 4} : Finset (ZMod 8)) 0 0 := by unfold IsPDS; decide
example : ¬ IsPDS ({1, 7} : Finset (ZMod 8)) 0 1 := by unfold IsPDS; decide

-- The rook-graph PDS behind O22 (O22 translated by -(5,1)): two lines through 0 in C6 × C6.
def rook : Finset (ZMod 6 × ZMod 6) :=
  {(1, 5), (2, 4), (3, 3), (4, 2), (5, 1), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5)}

theorem rook_pds : IsPDS rook 4 2 := by unfold IsPDS; decide +kernel
example : HasSDS (ZMod 6 × ZMod 6) 11 2 := rook_pds.hasSDS rfl
-- Its minusZero is exactly O22 translated: −1 at 0, +1 on rook.
example : minusZero rook (0, 0) = -1 ∧ minusZero rook (1, 5) = 1 ∧ minusZero rook (1, 1) = 0 := by
  decide

#print axioms IsPDS.isSDS_minusZero
#print axioms IsPDS.hasSDS
#print axioms rook_pds
