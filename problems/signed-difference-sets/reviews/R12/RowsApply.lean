import SignedDifferenceSets.SelfConjugacyRows.Part01

/-! Refuter: chunk theorem statement, axioms, and instantiation to the rows' own groups. -/

open SignedDifferenceSets SignedDifferenceSets.SelfConjugacyRows

set_option pp.funBinderTypes true in
#check @part01_not_hasSDS
#check @not_hasSDS_of_moments
#check @MomentsOk
#print axioms part01_not_hasSDS
#print axioms part01_kills
#print axioms ScCert.not_hasSDS
#print axioms not_hasSDS_of_moments
#print axioms momentsOk_of_congr

-- N30 C5, H = G
example : ¬ HasSDS (ZMod 2 × ZMod 10) 11 2 :=
  part01_not_hasSDS (x := (⟨30, [2, 10], 11, 2⟩, ⟨3, 1, 2, [2, 10], 0⟩)) (by decide +kernel) _
-- N326 C6, s = 11, H = ZMod 2 × ZMod 6
example : ¬ HasSDS (ZMod 2 × ZMod 24) 27 2 :=
  part01_not_hasSDS (x := (⟨326, [2, 24], 27, 2⟩, ⟨5, 1, 1, [2, 6], 11⟩)) (by decide +kernel) _
-- N524 C6, cyclic, s = 22
example : ¬ HasSDS (ZMod 57) 36 8 :=
  part01_not_hasSDS (x := (⟨524, [57], 36, 8⟩, ⟨2, 1, 9, [57], 22⟩)) (by decide +kernel) _
-- N724 C5, six factors
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) 46 10 :=
  part01_not_hasSDS (x := (⟨724, [2, 2, 2, 2, 2, 2], 46, 10⟩, ⟨3, 1, 1, [2, 2, 2, 2, 2, 2], 0⟩))
    (by decide +kernel) _

-- Controls, each must FAIL: wrong k; wrong group order of factors (2x10 vs 10x2 is not defeq).
example : ¬ HasSDS (ZMod 2 × ZMod 10) 12 2 :=
  part01_not_hasSDS (x := (⟨30, [2, 10], 11, 2⟩, ⟨3, 1, 2, [2, 10], 0⟩)) (by decide +kernel) _
example : ¬ HasSDS (ZMod 10 × ZMod 2) 11 2 :=
  part01_not_hasSDS (x := (⟨30, [2, 10], 11, 2⟩, ⟨3, 1, 2, [2, 10], 0⟩)) (by decide +kernel) _
-- Control: a fake entry not in the list must fail membership.
example : ¬ HasSDS (ZMod 2 × ZMod 10) 11 3 :=
  part01_not_hasSDS (x := (⟨30, [2, 10], 11, 3⟩, ⟨3, 1, 2, [2, 10], 0⟩)) (by decide +kernel) _
