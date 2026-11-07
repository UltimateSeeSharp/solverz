import SignedDifferenceSets.MarkedCountsRows.Part01
import SignedDifferenceSets.MarkedCountsRows.Part03
open SignedDifferenceSets
example : ¬ HasSDS (ZMod 2 × ZMod 40) 72 36 :=
  MarkedCountsRows.part01_not_hasSDS
    (x := (⟨1214, [2, 40], 72, 36⟩, ⟨⟨3, 1, 2, [2, 10], 54⟩, [⟨-1, 0, 36, 9⟩]⟩)) (by decide +kernel) _
example : ¬ HasSDS (ZMod 496) 495 54 :=
  MarkedCountsRows.part03_not_hasSDS
    (x := (⟨69990, [496], 495, 54⟩, ⟨⟨3, 1, 15, [62], 165⟩, [⟨1, -6, 72, 9⟩, ⟨1, 6, 72, 9⟩]⟩)) (by decide +kernel) _
