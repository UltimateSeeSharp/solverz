module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N20453: a (277, 208, 17) SDS in C₂₇₇

Open in Gordon's table (`SDS(277,208,17,[277])`, 2026-11-05). The set is object O94
(`objects/O94.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 10 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N20453

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O94's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x165b25d78a707254edce57fe028a333c0d212c0f3314501ffa9cedca9383947ae9369b

set_option linter.style.longLine false in
/-- Object O94's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x8841a00758485a3101000012c70c80150989150c82822c0056110040434000500c120

/-- Object O94: the sign of each element. -/
def sds : ZMod 277 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 277) 208 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 26. -/
theorem shifts1 : allFrom (shiftOk (ZMod 277) 17 plus minus) 0 27 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 27 to 54. -/
theorem shifts2 : allFrom (shiftOk (ZMod 277) 17 plus minus) 27 28 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 55 to 82. -/
theorem shifts3 : allFrom (shiftOk (ZMod 277) 17 plus minus) 55 28 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 83 to 109. -/
theorem shifts4 : allFrom (shiftOk (ZMod 277) 17 plus minus) 83 27 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 110 to 137. -/
theorem shifts5 : allFrom (shiftOk (ZMod 277) 17 plus minus) 110 28 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 138 to 165. -/
theorem shifts6 : allFrom (shiftOk (ZMod 277) 17 plus minus) 138 28 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 166 to 192. -/
theorem shifts7 : allFrom (shiftOk (ZMod 277) 17 plus minus) 166 27 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 193 to 220. -/
theorem shifts8 : allFrom (shiftOk (ZMod 277) 17 plus minus) 193 28 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 221 to 248. -/
theorem shifts9 : allFrom (shiftOk (ZMod 277) 17 plus minus) 221 28 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 249 to 276. -/
theorem shifts10 : allFrom (shiftOk (ZMod 277) 17 plus minus) 249 28 = true := by
  decide +kernel

theorem isSDS : IsSDS 208 17 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  have h := allFrom_append h shifts7
  have h := allFrom_append h shifts8
  have h := allFrom_append h shifts9
  have h := allFrom_append h shifts10
  exact isSDS_of_checkSplit count h

/-- N20453: C₂₇₇ has a signed difference set with
parameters (277, 208, 17). -/
theorem hasSDS :
    HasSDS (ZMod 277) 208 17 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N20453
