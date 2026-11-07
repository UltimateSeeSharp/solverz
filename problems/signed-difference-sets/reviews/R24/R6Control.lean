import SignedDifferenceSets.SylowRows

open SignedDifferenceSets

-- C1 wrong k: must fail
example : ¬ HasSDS (ZMod 88) 79 (14) :=
  sylowRows1_not_hasSDS (x := (⟨1539, [88], 78, 14⟩, ⟨2, 4, 6, 2, 3, 36, [8]⟩)) (by decide +kernel) inferInstance
-- C2 an existing SDS (O13, C2 x C16, (32,20,4), s = 12): Kills must be false
example : SyCert.Kills ⟨0, [2, 16], 20, 4⟩ ⟨2, 8, 4, 1, 5, 12, [2, 16]⟩ := by decide +kernel
-- C3 q one too big for e (2(qφ+1) ≤ eφ fails): must fail
example : SyCert.Kills ⟨1539, [88], 78, 14⟩ ⟨2, 4, 6, 3, 3, 36, [8]⟩ := by decide +kernel
-- C4 (2,3) not in maPairs, ds [8] with r = 3: must fail
example : SyCert.Kills ⟨1539, [88], 78, 14⟩ ⟨2, 3, 6, 2, 3, 36, [8]⟩ := by decide +kernel
-- C5 quotient not a p-power (ds [4,1] ok but [6]): must fail
example : SyCert.Kills ⟨0, [12], 11, 2⟩ ⟨2, 2, 0, 0, 1, 3, [6]⟩ := by decide +kernel
-- C6 positive control: the real cert of N1539 is decided true
example : SyCert.Kills ⟨1539, [88], 78, 14⟩ ⟨2, 4, 6, 2, 3, 36, [8]⟩ := by decide +kernel
