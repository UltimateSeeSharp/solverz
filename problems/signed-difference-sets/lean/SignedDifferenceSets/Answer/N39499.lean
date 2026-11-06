module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N39499: a (379, 190, 93) SDS in C₃₇₉

Open in Gordon's table (`SDS(379,190,93,[379])`, 2026-11-05). The set is object O89
(`objects/O89.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 12 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N39499

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O89's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O89's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x4e429fe26d4452a6920ddb9fcdf233c768f7af090d7478555e1d14f6f0a10e91c33b04c06244fb69ab5dd49b806bd8c

/-- Object O89: the sign of each element. -/
def sds : ZMod 379 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 379) 190 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 30. -/
theorem shifts1 : allFrom (shiftOk (ZMod 379) 93 plus minus) 0 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 31 to 62. -/
theorem shifts2 : allFrom (shiftOk (ZMod 379) 93 plus minus) 31 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 63 to 93. -/
theorem shifts3 : allFrom (shiftOk (ZMod 379) 93 plus minus) 63 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 94 to 125. -/
theorem shifts4 : allFrom (shiftOk (ZMod 379) 93 plus minus) 94 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 126 to 156. -/
theorem shifts5 : allFrom (shiftOk (ZMod 379) 93 plus minus) 126 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 157 to 188. -/
theorem shifts6 : allFrom (shiftOk (ZMod 379) 93 plus minus) 157 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 189 to 220. -/
theorem shifts7 : allFrom (shiftOk (ZMod 379) 93 plus minus) 189 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 221 to 251. -/
theorem shifts8 : allFrom (shiftOk (ZMod 379) 93 plus minus) 221 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 252 to 283. -/
theorem shifts9 : allFrom (shiftOk (ZMod 379) 93 plus minus) 252 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 284 to 314. -/
theorem shifts10 : allFrom (shiftOk (ZMod 379) 93 plus minus) 284 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 315 to 346. -/
theorem shifts11 : allFrom (shiftOk (ZMod 379) 93 plus minus) 315 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 347 to 378. -/
theorem shifts12 : allFrom (shiftOk (ZMod 379) 93 plus minus) 347 32 = true := by
  decide +kernel

theorem isSDS : IsSDS 190 93 sds := by
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
  exact isSDS_of_checkSplit count h

/-- N39499: C₃₇₉ has a signed difference set with
parameters (379, 190, 93). -/
theorem hasSDS :
    HasSDS (ZMod 379) 190 93 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N39499
