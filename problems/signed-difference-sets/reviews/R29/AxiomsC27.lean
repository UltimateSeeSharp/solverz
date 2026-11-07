import SignedDifferenceSets.UnramifiedRows
open SignedDifferenceSets
#print axioms SignedDifferenceSets.IsSDS.totient_mul_le
#print axioms SignedDifferenceSets.DescentRowCert.not_hasSDS
#print axioms SignedDifferenceSets.unramifiedRows1_not_hasSDS
#print axioms SignedDifferenceSets.unramifiedRows2_not_hasSDS
#print axioms SignedDifferenceSets.unramifiedRows3_not_hasSDS
#print axioms SignedDifferenceSets.unramifiedRows4_not_hasSDS
#print axioms SignedDifferenceSets.unramifiedRows5_not_hasSDS
#check @SignedDifferenceSets.IsSDS.totient_mul_le
#check @SignedDifferenceSets.unramifiedRows1_not_hasSDS
#print SignedDifferenceSets.DescentRowCert.Kills
-- row count per chunk (must total 259)
#eval [unramifiedRows1.length, unramifiedRows2.length, unramifiedRows3.length, unramifiedRows4.length, unramifiedRows5.length]
-- an instance used by a row: N9792, the row beyond Schmidt's F(100,121) = 20
example : ¬ HasSDS (Grp [2, 100]) 139 18 :=
  unramifiedRows1_not_hasSDS (x := (⟨9792, [2, 100], 139, 18⟩, ⟨100, 10, [0, 1], [0, 1]⟩)) (by decide +kernel) _
-- Schmidt's F = 20 does not kill it
example : ¬ DescentRowCert.Kills ⟨9792, [2, 100], 139, 18⟩ ⟨100, 20, [0, 1], [0, 1]⟩ := by decide +kernel
