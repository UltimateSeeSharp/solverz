import SignedDifferenceSets.RealCharsRows
open SignedDifferenceSets
-- explicit row goals from instances.csv, discharged by the list theorem
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 6) 18 2 :=
  realCharsRows_not_hasSDS (x := (⟨46, [2, 2, 6], 18, 2⟩, ⟨3, 8, 4⟩)) (by decide +kernel) _
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 62) 396 140 :=
  realCharsRows_not_hasSDS (x := (⟨69846, [2, 2, 2, 62], 396, 140⟩, ⟨4, 264, 16⟩)) (by decide +kernel) _
example : ¬ HasSDS (ZMod 6 × ZMod 6 × ZMod 6) 110 46 :=
  realCharsRows_not_hasSDS (x := (⟨11324, [6, 6, 6], 110, 46⟩, ⟨3, 100, 8⟩)) (by decide +kernel) _
-- a wrong group must not typecheck against the same certificate
example : ¬ HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 3) 18 2 :=
  realCharsRows_not_hasSDS (x := (⟨46, [2, 2, 6], 18, 2⟩, ⟨3, 8, 4⟩)) (by decide +kernel) _
