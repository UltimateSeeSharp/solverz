import SignedDifferenceSets.DescentRows
import SignedDifferenceSets.MaDescentFull
import SignedDifferenceSets.Contraction

open SignedDifferenceSets

#print axioms SignedDifferenceSets.Ma.dvd_contract_sub
#print axioms SignedDifferenceSets.dvd_pair_term
#print axioms SignedDifferenceSets.not_hasSDS_of_maDescent
#print axioms SignedDifferenceSets.DescentCert.not_hasSDS
#print axioms SignedDifferenceSets.descentRows1_not_hasSDS
#print axioms SignedDifferenceSets.descentRows2_not_hasSDS
#print axioms SignedDifferenceSets.descentRows3_not_hasSDS
#print axioms SignedDifferenceSets.descentRows4_not_hasSDS
#print axioms SignedDifferenceSets.descentRows5_not_hasSDS
#print axioms SignedDifferenceSets.IsSDS.comp_addEquiv
#print axioms SignedDifferenceSets.contract_comp
#print axioms SignedDifferenceSets.hasSDS_half_of_maDescent
#print axioms SignedDifferenceSets.HalfCert.not_hasSDS
#print axioms SignedDifferenceSets.IsSDS.sum_abs_contract_le
#print axioms SignedDifferenceSets.IsSDS.sum_abs_contract_parity
#print axioms SignedDifferenceSets.card_fibre_eq

-- statements as elaborated
#check @SignedDifferenceSets.not_hasSDS_of_maDescent
#check @SignedDifferenceSets.hasSDS_half_of_maDescent
#check @SignedDifferenceSets.IsSDS.sum_abs_contract_parity
#print SignedDifferenceSets.DescentCert.Kills

-- no chunk beyond 5
#check descentRows5
example : descentRows1.length + descentRows2.length + descentRows3.length + descentRows4.length
    + descentRows5.length = 177 := by decide

-- positive use: no SDS (16, 6, 2) in C16 (parity at c = 1: 2s - (k + lam) = 4, -2s - 8 = -20)
example (inst : Fintype (Grp [16])) : ¬ @HasSDS (Grp [16]) _ inst 6 2 :=
  DescentCert.not_hasSDS (w := ⟨0, [16], 6, 2⟩) (c := ⟨8, 1, 6, [1], [[1], [1]], [[1], [0]]⟩)
    (by decide +kernel) inst

-- negative: the cert form cannot kill CW(4,4) in C4 (O3) at c = 1, nor (16,6,2) in C16 with r = 4 (c = 2:
-- 2*6 - (6 + 2*3) = 0)
example : ¬ DescentCert.Kills ⟨0, [4], 4, 0⟩ ⟨2, 1, 2, [1], [[1], [1]], [[1], [0]]⟩ := by decide +kernel
example : ¬ DescentCert.Kills ⟨0, [16], 6, 2⟩ ⟨4, 1, 6, [1], [[1], [1]], [[1], [0]]⟩ := by decide +kernel
-- the r = 4 cert is well formed (map and preimages fine), so the negative above is arithmetic, not a malformed map
example : MapOk [16] [4 * 2, 1] [[1], [1]] ∧ SurjCert [16] [4 * 2, 1] [[1], [1]] [[1], [0]] := by decide +kernel
example : MapOk [4] [2 * 2, 1] [[1], [1]] ∧ SurjCert [4] [2 * 2, 1] [[1], [1]] [[1], [0]] := by decide +kernel
