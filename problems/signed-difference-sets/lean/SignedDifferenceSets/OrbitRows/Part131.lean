module

public import SignedDifferenceSets.OrbitSearchSplit
public import SignedDifferenceSets.OrbitRows.Part130

/-!
# Rows killed by C9 and the orbit search split into slices, part 131

2 open rows (N63096, N27026) that E10/E11 exhausted, n coprime to v (2 with n squarefree, through
C15; 0 with n not squarefree, through C9 for every n), each closed by the orbit search split at a
depth into slices of its frontier. Slices of the search for N33284 (closed in part 132). Generated
by `solver/orbitsplit.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.OrbitRows

set_option maxRecDepth 100000
-- One declaration at a time: the slices' kernel checks would otherwise run in parallel and their
-- memory add up.
set_option Elab.async false

theorem n63096_slice1 : orbitSlice [473] 449 70 379 183 7 1 3 = true := by
  decide +kernel

theorem n63096_slice2 : orbitSlice [473] 449 70 379 183 7 3 6 = true := by
  decide +kernel

theorem n63096_slice3 : orbitSlice [473] 449 70 379 183 7 6 9 = true := by
  decide +kernel

theorem n63096_slice4 : orbitSlice [473] 449 70 379 183 7 9 13 = true := by
  decide +kernel

theorem n63096_slice5 : orbitSlice [473] 449 70 379 183 7 13 24 = true := by
  decide +kernel

theorem n63096_slice6 : orbitSlice [473] 449 70 379 183 7 24 27 = true := by
  decide +kernel

theorem n63096_slice7 : orbitSlice [473] 449 70 379 183 7 27 39 = true := by
  decide +kernel

theorem n63096_slice8 : orbitSlice [473] 449 70 379 183 7 39 46 = true := by
  decide +kernel

theorem n63096_slice9 : orbitSlice [473] 449 70 379 183 7 46 57 = true := by
  decide +kernel

theorem n63096_slice10 : orbitSlice [473] 449 70 379 183 7 57 78 = true := by
  decide +kernel

/-- N63096: 21 orbits of x ↦ 379x, 3300 sign choices to evaluate, 47512 nodes; split at depth 7 into
11 slices. -/
theorem n63096_not_hasSDS : ¬ HasSDS (ZMod 473) 449 70 :=
  not_hasSDS_of_orbitSlices (ms := [473]) (t := 379) (s := 183) (by decide +kernel)
    (orbitExhaust_of_slices (ms := [473]) (k := 449) (lam := 70) (t := 379)
      (s := 183) (d := 7)
      [1, 3, 6, 9, 13, 24, 27, 39, 46, 57, 78]
      (by decide +kernel) <|
      .cons n63096_slice0 <|
      .cons n63096_slice1 <|
      .cons n63096_slice2 <|
      .cons n63096_slice3 <|
      .cons n63096_slice4 <|
      .cons n63096_slice5 <|
      .cons n63096_slice6 <|
      .cons n63096_slice7 <|
      .cons n63096_slice8 <|
      .cons n63096_slice9 <|
      .cons n63096_slice10 <|
      .single) _

theorem n27026_slice0 : orbitSlice [319] 265 8 257 53 4 0 2 = true := by
  decide +kernel

theorem n27026_slice1 : orbitSlice [319] 265 8 257 53 4 2 4 = true := by
  decide +kernel

theorem n27026_slice2 : orbitSlice [319] 265 8 257 53 4 4 9 = true := by
  decide +kernel

theorem n27026_slice3 : orbitSlice [319] 265 8 257 53 4 9 11 = true := by
  decide +kernel

theorem n27026_slice4 : orbitSlice [319] 265 8 257 53 4 11 16 = true := by
  decide +kernel

theorem n27026_slice5 : orbitSlice [319] 265 8 257 53 4 16 24 = true := by
  decide +kernel

/-- N27026: 15 orbits of x ↦ 257x, 3360 sign choices to evaluate, 35536 nodes; split at depth 4 into
6 slices. -/
theorem n27026_not_hasSDS : ¬ HasSDS (ZMod 319) 265 8 :=
  not_hasSDS_of_orbitSlices (ms := [319]) (t := 257) (s := 53) (by decide +kernel)
    (orbitExhaust_of_slices (ms := [319]) (k := 265) (lam := 8) (t := 257)
      (s := 53) (d := 4)
      [2, 4, 9, 11, 16, 24]
      (by decide +kernel) <|
      .cons n27026_slice0 <|
      .cons n27026_slice1 <|
      .cons n27026_slice2 <|
      .cons n27026_slice3 <|
      .cons n27026_slice4 <|
      .cons n27026_slice5 <|
      .single) _

theorem n33284_slice0 : orbitSlice [351] 50 1 7 20 12 0 38 = true := by
  decide +kernel

theorem n33284_slice1 : orbitSlice [351] 50 1 7 20 12 38 62 = true := by
  decide +kernel

theorem n33284_slice2 : orbitSlice [351] 50 1 7 20 12 62 77 = true := by
  decide +kernel

theorem n33284_slice3 : orbitSlice [351] 50 1 7 20 12 77 83 = true := by
  decide +kernel

theorem n33284_slice4 : orbitSlice [351] 50 1 7 20 12 83 89 = true := by
  decide +kernel

theorem n33284_slice5 : orbitSlice [351] 50 1 7 20 12 89 107 = true := by
  decide +kernel

theorem n33284_slice6 : orbitSlice [351] 50 1 7 20 12 107 125 = true := by
  decide +kernel

theorem n33284_slice7 : orbitSlice [351] 50 1 7 20 12 125 131 = true := by
  decide +kernel

theorem n33284_slice8 : orbitSlice [351] 50 1 7 20 12 131 155 = true := by
  decide +kernel

theorem n33284_slice9 : orbitSlice [351] 50 1 7 20 12 155 171 = true := by
  decide +kernel

theorem n33284_slice10 : orbitSlice [351] 50 1 7 20 12 171 176 = true := by
  decide +kernel

theorem n33284_slice11 : orbitSlice [351] 50 1 7 20 12 176 182 = true := by
  decide +kernel

theorem n33284_slice12 : orbitSlice [351] 50 1 7 20 12 182 197 = true := by
  decide +kernel

end SignedDifferenceSets.OrbitRows
