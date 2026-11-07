import SignedDifferenceSets.EisensteinCharsRows
open SignedDifferenceSets
#check @not_hasSDS_of_eisensteinChars
#print EisKills
#print axioms not_hasSDS_of_eisensteinChars
#print axioms IsSDS.charSumEis_norm
#print axioms charSumTr_cast
#print axioms charSumTr_neg
#print axioms neg_ne_self_of_three
#print axioms sum_charSumTr
#print axioms mem_eisTraces
-- trace lists
example : eisTraces 81 = [9, -9, 18, -18] := by decide
example : eisTraces 27 = [0, 0, 9, -9] := by decide
example : eisTraces 7 = [1, -1, 4, -4, 5, -5] := by decide
example : eisTraces 10 = [] := by decide
-- kills where the math says, silent on known SDS and on the trivial quotient
example : EisKills 9 21 81 := by decide        -- N1605 (90,85,4), H = C3^2
example : EisKills 3 0 6 := by decide          -- n = 6 not a norm of Z[w]
example : ¬ EisKills 9 9 9 := by decide        -- N19 (18,13,4) in C3 x C6 exists
example : ¬ EisKills 9 6 9 := by decide        -- O7 (27,10,1), H = C3^2
example : ¬ EisKills 9 0 9 := by decide        -- O5 with the true s = 0
example : ¬ EisKills 9 13 7 := by decide       -- Paley (27,13,6), s = 13
example : ¬ EisKills 9 15 9 := by decide       -- Spence (36,15,6): s = 15, n = 9
example : ¬ EisKills 1 5 7 := by decide        -- N = 1 never kills
example : ¬ EisKills 3 21 81 := by decide      -- N1605 at H = C3 survives (3 | 21)
-- rows module (oleans built by the researcher at 19:23)
#print axioms EcCert.not_hasSDS
#print axioms eisensteinCharsRows1_not_hasSDS
#print axioms eisensteinCharsRows2_not_hasSDS
#print axioms eisensteinCharsRows3_not_hasSDS
#check @eisensteinCharsRows1_not_hasSDS
theorem n1605 : ¬ HasSDS (ZMod 3 × ZMod 30) 85 4 :=
  EcCert.not_hasSDS (r := ⟨1605, [3, 30], 85, 4⟩) (c := ⟨[3, 3], 21⟩) (by decide +kernel) _
#print axioms n1605
-- a certificate with the wrong s or a non-dividing quotient is rejected
example : ¬ EcCert.Kills ⟨1605, [3, 30], 85, 4⟩ ⟨[3, 3], 20⟩ := by decide +kernel
example : ¬ EcCert.Kills ⟨1605, [3, 30], 85, 4⟩ ⟨[3, 9], 21⟩ := by decide +kernel
example : ¬ EcCert.Kills ⟨1605, [3, 30], 85, 4⟩ ⟨[3, 1], 21⟩ := by decide +kernel
