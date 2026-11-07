import SignedDifferenceSets.CompositeModulusRows
import SignedDifferenceSets.Answer.N3243
import SignedDifferenceSets.Answer.N31721
import SignedDifferenceSets.Answer.N31722
import SignedDifferenceSets.Answer.N3314
import SignedDifferenceSets.Answer.N3315
import SignedDifferenceSets.Answer.N32087
import SignedDifferenceSets.Answer.N32088
import SignedDifferenceSets.Answer.N658
import SignedDifferenceSets.Answer.N659
import SignedDifferenceSets.Answer.N660
import SignedDifferenceSets.Answer.N661
import SignedDifferenceSets.Answer.N663
import SignedDifferenceSets.Answer.N665
import SignedDifferenceSets.Answer.N736
import SignedDifferenceSets.Answer.N737
import SignedDifferenceSets.Answer.N740
import SignedDifferenceSets.Answer.N742
import SignedDifferenceSets.Answer.N26075
import SignedDifferenceSets.Answer.N47314
import SignedDifferenceSets.Answer.N1134
import SignedDifferenceSets.Answer.N9807
import SignedDifferenceSets.Answer.N58470

open SignedDifferenceSets

#print axioms SignedDifferenceSets.not_hasSDS_of_compositeModulus
#print axioms SignedDifferenceSets.CmCert.not_hasSDS
#print axioms SignedDifferenceSets.IsSDS.modulusProd_dvd
#print axioms SignedDifferenceSets.compositeModulusRows1_not_hasSDS
#print axioms SignedDifferenceSets.compositeModulusRows2_not_hasSDS
#print axioms SignedDifferenceSets.compositeModulusRows3_not_hasSDS
#print axioms SignedDifferenceSets.compositeModulusRows4_not_hasSDS
#print axioms SignedDifferenceSets.Answer.N3243.hasSDS
#print axioms SignedDifferenceSets.Answer.N31721.hasSDS
#print axioms SignedDifferenceSets.Answer.N31722.hasSDS
#print axioms SignedDifferenceSets.Answer.N3314.hasSDS
#print axioms SignedDifferenceSets.Answer.N3315.hasSDS
#print axioms SignedDifferenceSets.Answer.N32087.hasSDS
#print axioms SignedDifferenceSets.Answer.N32088.hasSDS
#print axioms SignedDifferenceSets.Answer.N658.hasSDS
#print axioms SignedDifferenceSets.Answer.N659.hasSDS
#print axioms SignedDifferenceSets.Answer.N660.hasSDS
#print axioms SignedDifferenceSets.Answer.N661.hasSDS
#print axioms SignedDifferenceSets.Answer.N663.hasSDS
#print axioms SignedDifferenceSets.Answer.N665.hasSDS
#print axioms SignedDifferenceSets.Answer.N736.hasSDS
#print axioms SignedDifferenceSets.Answer.N737.hasSDS
#print axioms SignedDifferenceSets.Answer.N740.hasSDS
#print axioms SignedDifferenceSets.Answer.N742.hasSDS
#print axioms SignedDifferenceSets.Answer.N26075.hasSDS
#print axioms SignedDifferenceSets.Answer.N47314.hasSDS
#print axioms SignedDifferenceSets.Answer.N1134.hasSDS
#print axioms SignedDifferenceSets.Answer.N9807.hasSDS
#print axioms SignedDifferenceSets.Answer.N58470.hasSDS
#check @SignedDifferenceSets.Answer.N3243.hasSDS
#check @SignedDifferenceSets.Answer.N658.hasSDS
#check @SignedDifferenceSets.Answer.N742.hasSDS
#check @SignedDifferenceSets.Answer.N26075.hasSDS
#check @SignedDifferenceSets.Answer.N47314.hasSDS
#check @SignedDifferenceSets.Answer.N1134.hasSDS
#check @SignedDifferenceSets.Answer.N9807.hasSDS
#check @SignedDifferenceSets.Answer.N58470.hasSDS
#check @not_hasSDS_of_compositeModulus
#check @CmCert.not_hasSDS

/-- N5513 instantiates to C₃ × C₅₁. -/
example : ¬ HasSDS (ZMod 3 × ZMod 51) 112 12 :=
  compositeModulusRows1_not_hasSDS
    (x := (⟨5513, [3, 51], 112, 12⟩, ⟨[1, 17], [(2, 4, 1), (5, 8, 1)], 44⟩)) (by decide) inferInstance

/-- N68801 instantiates to C₄₉₃. -/
example : ¬ HasSDS (ZMod 493) 412 187 :=
  compositeModulusRows4_not_hasSDS
    (x := (⟨68801, [493], 412, 187⟩, ⟨[17], [(3, 8, 1), (5, 8, 1)], 304⟩)) (by decide) inferInstance
