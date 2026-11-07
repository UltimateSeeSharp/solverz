import SignedDifferenceSets

open SignedDifferenceSets

#print axioms SignedDifferenceSets.Answer.N3.not_hasSDS
#print axioms SignedDifferenceSets.Answer.N3.mk_not_sds
#print axioms SignedDifferenceSets.Answer.N32.not_hasSDS
#print axioms SignedDifferenceSets.Answer.N32.no_vector
#print axioms SignedDifferenceSets.IsSDS.translate
#print axioms SignedDifferenceSets.IsSDS.neg
#print axioms SignedDifferenceSets.IsSDS.contract_autocorr
#print axioms SignedDifferenceSets.IsSDS.contract_sq
#print axioms SignedDifferenceSets.abs_contract_le

-- the statements as elaborated
#check @SignedDifferenceSets.Answer.N3.not_hasSDS
#check @SignedDifferenceSets.Answer.N32.not_hasSDS
#check @SignedDifferenceSets.IsSDS.translate
#check @SignedDifferenceSets.IsSDS.neg
#check @SignedDifferenceSets.IsSDS.contract_autocorr
#check @SignedDifferenceSets.IsSDS.contract_sq
#check @SignedDifferenceSets.abs_contract_le
#print SignedDifferenceSets.IsSDS
#print SignedDifferenceSets.HasSDS

-- sanity: the theorems' statements are not vacuous: a known SDS passes, and with lam = -1 the
-- (9,8,·) case on C3 x C3 exists, so N3's negation is not about an empty predicate
example : HasSDS (ZMod 3 × ZMod 3) 8 (-1) :=
  ⟨fun p => ![![-1, -1, 1], ![-1, -1, 1], ![1, 1, 0]] p.1 p.2, by decide⟩
-- the Gordon (18,13,4) set in C3 x C6 = C3 x C3 x C2 (G_rep check below) exists in some product
