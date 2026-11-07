import SignedDifferenceSets.OrbitSearchWitt
import SignedDifferenceSets.Tests.MultiplierWitt
import SignedDifferenceSets.OrbitRows.Part33
import SignedDifferenceSets.OrbitRows.Part55
import SignedDifferenceSets.OrbitRows.Part59

set_option autoImplicit false

/-! Refuter I13: axioms, exact statements, and negative controls on known-exists rows with n not squarefree. -/

open SignedDifferenceSets

#print axioms dvd_cross
#print axioms IsSDS.exists_multiplier'
#print axioms IsSDS.exists_translate_fixed'
#print axioms IsSDS.exists_translate_fixed_contract'
#print axioms not_hasSDS_of_orbitRow'
#print axioms OrbitRows.n1157_not_hasSDS
#print axioms OrbitRows.n15759_not_hasSDS
#print axioms OrbitRows.n4630_not_hasSDS
#check @IsSDS.exists_translate_fixed'
#check @IsSDS.exists_translate_fixed_contract'
#check @OrbitRows.n1157_not_hasSDS
#check @OrbitRows.n4630_not_hasSDS
#print OrbitRow'

-- Known sets, n not squarefree (C20 (20,11,2) n = 9; C23 (23,12,4) n = 8; C51 (51,19,3) n = 16, O69;
-- C7 (7,4,0) n = 4, O2): the exhaust the parts use must fail on them.
example : orbitExhaust [20] 11 2 3 7 = false := by decide +kernel
example : orbitExhaust [23] 12 4 2 10 = false := by decide +kernel
example : orbitExhaust [51] 19 3 2 13 = false := by decide +kernel
example : orbitExhaust [7] 4 0 2 2 = false := by decide +kernel
-- and OrbitRow' with them is false
example : ¬ OrbitRow' [51] 19 3 2 13 := by decide +kernel
