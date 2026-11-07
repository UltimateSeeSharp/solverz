module

public import SignedDifferenceSets.OrbitSearchSplit

/-!
# Tests of the orbit search split into slices (I16)

Rows closed through both wrappers (C15 for squarefree `n`, C9 for every `n`), node counts as
`solver/orbitsplit.py`'s mirror lists them, and controls: the top rejects a bound below the
node count, and on rows with a known SDS the slice holding it fails.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests.OrbitSearchSplit

/-! ### Kills -/

theorem n898_slice0 : orbitSlice [71] 11 1 57 9 3 0 3 = true := by decide +kernel

theorem n898_slice1 : orbitSlice [71] 11 1 57 9 3 3 6 = true := by decide +kernel

/-- N898, (71, 11, 1) in C₇₁, `n = 10` squarefree: `x ↦ 57x` has 15 orbits, 91 sign choices
reach the leaves; split at depth 3 (6 nodes) into two slices. -/
example : ¬ HasSDS (ZMod 71) 11 1 :=
  not_hasSDS_of_orbitSlices (ms := [71]) (t := 57) (s := 9) (by decide +kernel)
    (orbitExhaust_of_slices (ms := [71]) (k := 11) (lam := 1) (t := 57) (s := 9) (d := 3) [3, 6]
      (by decide +kernel) (.cons n898_slice0 (.cons n898_slice1 .single))) _

theorem n486_slice0 : orbitSlice [55] 40 4 4 16 2 0 1 = true := by decide +kernel

theorem n486_slice1 : orbitSlice [55] 40 4 4 16 2 1 3 = true := by decide +kernel

/-- N486, (55, 40, 4) in C₅₅, `n = 36` not squarefree: `x ↦ 4x` has 9 orbits, 48 sign choices
reach the leaves; split at depth 2 (3 nodes) into two slices. -/
example : ¬ HasSDS (ZMod 55) 40 4 :=
  not_hasSDS_of_orbitSlices' (ms := [55]) (t := 4) (s := 16) (by decide +kernel)
    (orbitExhaust_of_slices (ms := [55]) (k := 40) (lam := 4) (t := 4) (s := 16) (d := 2) [1, 3]
      (by decide +kernel) (.cons n486_slice0 (.cons n486_slice1 .single))) _

/-! ### Node counts -/

-- N898 has 6 nodes at depth 3, as the mirror lists: the top takes 6 and rejects 5.
example : orbitTop [71] 11 57 9 3 6 = true := by decide +kernel

example : orbitTop [71] 11 57 9 3 5 = false := by decide +kernel

-- So a cut list ending before the last node cannot pass the top.
example : orbitTop [71] 11 57 9 3 (OrbitSearch.endCut 0 [3, 5]) = false := by decide +kernel

/-! ### Controls: rows with an SDS -/

-- N6 exists ((11, 6, 1), Paley and zero; `t = 5`, `s = 4`): one level down, the middle node
-- (the zero element marked `−`) holds it.
example : orbitSlice [11] 6 1 5 4 1 0 1 = true := by decide +kernel

example : orbitSlice [11] 6 1 5 4 1 1 2 = false := by decide +kernel

example : orbitSlice [11] 6 1 5 4 1 2 3 = true := by decide +kernel

-- N24 exists ((19, 10, 3); `t = 7`, `s = 8`): the slice of all 3 nodes at depth 2 fails.
example : orbitSlice [19] 10 3 7 8 2 0 3 = false := by decide +kernel

end SignedDifferenceSets.Tests.OrbitSearchSplit
