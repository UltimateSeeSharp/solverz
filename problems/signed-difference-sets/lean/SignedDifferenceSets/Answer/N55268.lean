module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N55268: a (443, 222, 109) SDS in C₄₄₃

Open in Gordon's table (`SDS(443,222,109,[443])`, 2026-11-05). The set is object O90
(`objects/O90.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 14 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N55268

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O90's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O90's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x586ec2521fe3d9b6b91542e1097d74d2347cfdd8dfe247a9ae78c54cd5ce18a6a1db804e440c1d3b4d1416f78bd576292643807b5bc89e4

/-- Object O90: the sign of each element. -/
def sds : ZMod 443 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 443) 222 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 30. -/
theorem shifts1 : allFrom (shiftOk (ZMod 443) 109 plus minus) 0 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 31 to 62. -/
theorem shifts2 : allFrom (shiftOk (ZMod 443) 109 plus minus) 31 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 63 to 93. -/
theorem shifts3 : allFrom (shiftOk (ZMod 443) 109 plus minus) 63 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 94 to 125. -/
theorem shifts4 : allFrom (shiftOk (ZMod 443) 109 plus minus) 94 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 126 to 157. -/
theorem shifts5 : allFrom (shiftOk (ZMod 443) 109 plus minus) 126 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 158 to 188. -/
theorem shifts6 : allFrom (shiftOk (ZMod 443) 109 plus minus) 158 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 189 to 220. -/
theorem shifts7 : allFrom (shiftOk (ZMod 443) 109 plus minus) 189 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 221 to 252. -/
theorem shifts8 : allFrom (shiftOk (ZMod 443) 109 plus minus) 221 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 253 to 283. -/
theorem shifts9 : allFrom (shiftOk (ZMod 443) 109 plus minus) 253 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 284 to 315. -/
theorem shifts10 : allFrom (shiftOk (ZMod 443) 109 plus minus) 284 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 316 to 347. -/
theorem shifts11 : allFrom (shiftOk (ZMod 443) 109 plus minus) 316 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 348 to 378. -/
theorem shifts12 : allFrom (shiftOk (ZMod 443) 109 plus minus) 348 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 379 to 410. -/
theorem shifts13 : allFrom (shiftOk (ZMod 443) 109 plus minus) 379 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 411 to 442. -/
theorem shifts14 : allFrom (shiftOk (ZMod 443) 109 plus minus) 411 32 = true := by
  decide +kernel

theorem isSDS : IsSDS 222 109 sds := by
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
  have h := allFrom_append h shifts11
  have h := allFrom_append h shifts12
  have h := allFrom_append h shifts13
  have h := allFrom_append h shifts14
  exact isSDS_of_checkSplit count h

/-- N55268: C₄₄₃ has a signed difference set with
parameters (443, 222, 109). -/
theorem hasSDS :
    HasSDS (ZMod 443) 222 109 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N55268
