module

public import SignedDifferenceSets.MaLemma
public import SignedDifferenceSets.MaRows.Part01

/-!
# Tests for C21's row checks (`PolyCert`, `LinearMaps`, `MaCheck`)

The polynomial lists compute what they should, `MaCert` accepts the `(2, 1)` certificate and
rejects a wrong one, and `CycloFacts.mul` climbs the tower; the forms `x ↦ (x mod 8, x mod 3)` on
`ℤ₂₄` (row N48's quotient) are a valid surjection with preimages `9` and `16`, and the check
refuses a bad form or preimage; row N323 (`SDS(48, 24, 8)` in `ℤ₄₈`) is killed, given `MaRule`
and by `maRule`, while the circulant weighing matrix `CW(4, 4)` (which exists, with `2c = p^b`)
is not killed.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

/-! Polynomials. -/

example : evalL (3 : ℤ) [1, 2] = 7 := by decide

example : mulL [1, 1] [-1, 1] = [-1, 0, 1] := by decide

example : powL [-1, 1] 2 = [1, -2, 1] := by decide

/-- `Ψ = 1 + X² + X⁴` at `(p, r) = (3, 2)`, with trailing zeros. -/
example : psiL 3 2 = [1, 0, 1, 0, 1, 0, 0] := by decide

example : ofLimbs [1, 5] = 10 ^ 80 + 5 := by decide

/-- `(X − 1)·(−1) + (1 + X)·1 = 2` and `X − 1 = 2·(−1) + (1 + X)·1`. -/
example : MaCert 2 1 [-1] [1] [-1] [1] := by decide +kernel

example : ¬ MaCert 2 1 [1] [1] [-1] [1] := by decide +kernel

example : ¬ MaCert 3 1 [1] [0] [0] [1] := by decide +kernel

example : CycloFacts 2 1 := MaCert.cycloFacts (f := [-1]) (g := [1]) (u := [-1]) (w := [1])
  (by decide +kernel)

/-- The tower step, from `(3, 3)` to `(3, 9)`. -/
example : CycloFacts 3 9 := MaRows.cycloFactsP3R3.mul (by norm_num) (by norm_num)

/-! Linear maps: `ℤ₂₄ → ℤ₈ × ℤ₃`. -/

example : FormOk 8 [1] [24] := by decide

example : ¬ FormOk 16 [1] [24] := by decide

example : linMap [24] [8, 3] [[1], [1]] (by decide) (Grp.ofList [24] [9]) =
    Grp.ofList [8, 3] [1, 0] := by
  rw [linMap_ofList]
  decide

example : SurjCert [24] [8, 3] [[1], [1]] [[9], [16]] := by decide

example : ¬ SurjCert [24] [8, 3] [[1], [1]] [[1], [16]] := by decide

example : Function.Surjective (linMap [24] [8, 3] [[1], [1]] (by decide)) :=
  linMap_surjective (P := [[9], [16]]) _ (by decide)

/-! Rows. -/

/-- Row N323's certificate: `p = 2`, `ℤ₄₈ → ℤ₁₆ × ℤ₃`, `k − λ = 16 = 2⁴`, `b = 2`, `c = 1`. -/
def certN323 : MaRowCert := ⟨2, 8, 1, 4, 2, [3], [[1], [1]], [[33], [16]]⟩

example : certN323.Kills ⟨323, [48], 24, 8⟩ := by decide +kernel

example (hrule : MaRule) : ¬ HasSDS (ZMod 48) 24 8 :=
  MaRowCert.not_hasSDS hrule (w := ⟨323, [48], 24, 8⟩) (c := certN323) (by decide +kernel)
    MaRows.cycloFactsP2R8 _

example (hrule : MaRule) : ¬ HasSDS (ZMod 48) 24 8 :=
  MaRows.part01_not_hasSDS hrule (x := (⟨323, [48], 24, 8⟩, certN323)) (by decide +kernel) _

example : ¬ HasSDS (ZMod 48) 24 8 :=
  MaRows.part01_not_hasSDS maRule (x := (⟨323, [48], 24, 8⟩, certN323)) (by decide +kernel) _

/-- `2b ≤ e` fails. -/
example : ¬ (⟨2, 8, 1, 4, 3, [3], [[1], [1]], [[33], [16]]⟩ : MaRowCert).Kills
    ⟨323, [48], 24, 8⟩ := by decide +kernel

/-- A preimage that misses. -/
example : ¬ (⟨2, 8, 1, 4, 2, [3], [[1], [1]], [[1], [16]]⟩ : MaRowCert).Kills
    ⟨323, [48], 24, 8⟩ := by decide +kernel

/-- `CW(4, 4)` exists: `p = 2`, `b = 1`, `c = 1`, and `2c < p^b` fails. -/
example : ¬ (⟨2, 2, 1, 2, 1, [1], [[1], [1]], [[1], [0]]⟩ : MaRowCert).Kills ⟨0, [4], 4, 0⟩ := by
  decide +kernel

end SignedDifferenceSets.Tests
