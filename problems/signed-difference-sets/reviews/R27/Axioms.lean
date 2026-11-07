import SignedDifferenceSets.CosetRows.Part01
import SignedDifferenceSets.CosetRows.Part03
import SignedDifferenceSets.CosetRows.Part40
import SignedDifferenceSets.CosetSearchWitt

open SignedDifferenceSets

#print axioms SignedDifferenceSets.CosetSearch.valSearch_sound
#print axioms SignedDifferenceSets.CosetSearch.valSearch_of_frontier
#print axioms SignedDifferenceSets.CosetSearch.cosetCheck_sound
#print axioms SignedDifferenceSets.CosetSearch.cosetCheck_of_nodes
#print axioms SignedDifferenceSets.false_of_cosetCheck
#print axioms SignedDifferenceSets.cosetSearch_of_slices
#print axioms SignedDifferenceSets.c10Holds_of_squarefree
#print axioms SignedDifferenceSets.c10Holds_of_ne_zero
#print axioms SignedDifferenceSets.not_hasSDS_of_cosetSearch
#print axioms SignedDifferenceSets.not_hasSDS_of_cosetRow
#print axioms SignedDifferenceSets.not_hasSDS_of_cosetRow'
#print axioms SignedDifferenceSets.CosetRows.n27861_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n1978_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n14741_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n11103_not_hasSDS
#print axioms SignedDifferenceSets.CosetRows.n31630_not_hasSDS

#check @SignedDifferenceSets.CosetRows.n14741_not_hasSDS
#check @SignedDifferenceSets.CosetRows.n31630_not_hasSDS
#check @SignedDifferenceSets.not_hasSDS_of_cosetRow'

-- Controls: quotients of known SDSs (objects O36, O12, O24; exists row N31); C10 forces a fixed vector,
-- so the Lean search must return false.
example : cosetSearch [31] 7 193 168 5 191 = false := by decide +kernel
example : cosetSearch [7] 31 193 168 3 191 = false := by decide +kernel
example : cosetSearch [1, 19] 19 316 141 7 226 = false := by decide +kernel
example : cosetSearch [1, 7] 7 33 1 2 9 = false := by decide +kernel
example : cosetSearch [4] 5 11 2 3 7 = false := by decide +kernel
-- gcd(v, n) > 1, quotient prime to n: O61 (42, 18, 2) in C42, n = 16; O62 (75, 26, 1) in C5 x C15, n = 25.
example : cosetSearch [21] 2 18 2 2 10 = false := by decide +kernel
example : cosetSearch [7] 6 18 2 2 10 = false := by decide +kernel
example : cosetSearch [1, 3] 25 26 1 2 10 = false := by decide +kernel
-- Negative-sum form of a kill row (s replaced by -s must not matter: CosetRow requires s*s only).
example : CosetRow [175] [25] 7 52 8 16 (-38) := by decide +kernel
