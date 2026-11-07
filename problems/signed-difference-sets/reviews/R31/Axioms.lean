import SignedDifferenceSets.OrbitSearchSplit
import SignedDifferenceSets.OrbitRows.Part60
import SignedDifferenceSets.OrbitRows.Part62
import SignedDifferenceSets.OrbitRows.Part63
import SignedDifferenceSets.OrbitRows.Part67

set_option autoImplicit false

/-! Refuter xsplit: axioms, exact statements, a product-group control (N352, (49, 33, 1) on C7 x C7, exists). -/

open SignedDifferenceSets

#print axioms OrbitSearch.corrW_decode
#print axioms OrbitSearch.leafKilled_of_leafKilledN
#print axioms OrbitSearch.signSearch_of_signSearchN
#print axioms OrbitSearch.signSearchN_of_frontier
#print axioms OrbitSearch.all_of_slicesHold
#print axioms orbitCheck_eq
#print axioms orbitCheck_of_nodes
#print axioms orbitExhaust_of_slices
#print axioms not_hasSDS_of_orbitSlices
#print axioms not_hasSDS_of_orbitSlices'
#print axioms OrbitRows.n363_not_hasSDS
#print axioms OrbitRows.n71_not_hasSDS
#print axioms OrbitRows.n1512_not_hasSDS
#print axioms OrbitRows.n7332_not_hasSDS
#check @OrbitRows.n363_not_hasSDS
#check @OrbitRows.n71_not_hasSDS
#check @OrbitRows.n1512_not_hasSDS
#check @OrbitRows.n7332_not_hasSDS

example : Grp [88] = ZMod 88 := rfl
example : Grp [176] = ZMod 176 := rfl
example : Grp [3, 9] = (ZMod 3 × ZMod 9) := rfl

-- N352 exists; a translate is fixed by t = 2 (n = 32) with sign sum 9. Depth 10: 17,562 nodes (own count),
-- the solution lies under node 95 (own Lean-order frontier, front.py).
example : orbitTop [7, 7] 33 2 9 10 17562 = true := by decide +kernel
example : orbitTop [7, 7] 33 2 9 10 17561 = false := by decide +kernel
example : orbitSlice [7, 7] 33 1 2 9 10 95 96 = false := by decide +kernel
