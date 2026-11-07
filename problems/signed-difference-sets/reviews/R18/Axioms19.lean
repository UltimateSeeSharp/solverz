import SignedDifferenceSets.GaussChars
open SignedDifferenceSets
#check @not_hasSDS_of_gaussChars
#print axioms not_hasSDS_of_gaussChars
#print axioms IsSDS.charSum_mul_conj
#print axioms IsSDS.charSumRe_sq_add
#print axioms sum_charSumRe
#print axioms exists_pair_list
#print axioms mem_reachMod
#print axioms mem_gaussX
-- the kill fires where the math says, and not on parameters of known SDS
example : GaussKills 8 4 8 := by decide          -- N47: (24,18,2), H = C2 x C4
example : GaussKills 4 2 0 := by decide          -- (4,3,-1) in C4 (parity-impossible)
example : ¬ GaussKills 8 4 12 := by decide       -- (32,20,4), H = C2 x C4: SDS O13 exists
example : ¬ GaussKills 16 4 12 := by decide      -- (32,20,4), H = C4 x C4: O17
example : ¬ GaussKills 4 3 9 := by decide        -- (36,11,2), C3 x C12: O21
example : ¬ GaussKills 4 2 2 := by decide        -- (4,4,0) circulant Hadamard, C4: O3
example : ¬ GaussKills 1 3 5 := by decide        -- trivial H never kills when 1 | anything
