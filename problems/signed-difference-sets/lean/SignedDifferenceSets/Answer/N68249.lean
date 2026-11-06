module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N68249: a (491, 246, 121) SDS in C₄₉₁

Open in Gordon's table (`SDS(491,246,121,[491])`, 2026-11-05). The set is object O91
(`objects/O91.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 16 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N68249

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O91's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O91's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x5c5fc8514f7ed9accb11d4065c39265f5f31b8f85ccabfd29d1ea52df6c7dc41c904b5a8746b402acc5e0e27305059b63c59fd4772cca64810d75ec05c4

/-- Object O91: the sign of each element. -/
def sds : ZMod 491 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 491) 246 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 29. -/
theorem shifts1 : allFrom (shiftOk (ZMod 491) 121 plus minus) 0 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 30 to 60. -/
theorem shifts2 : allFrom (shiftOk (ZMod 491) 121 plus minus) 30 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 61 to 91. -/
theorem shifts3 : allFrom (shiftOk (ZMod 491) 121 plus minus) 61 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 92 to 121. -/
theorem shifts4 : allFrom (shiftOk (ZMod 491) 121 plus minus) 92 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 122 to 152. -/
theorem shifts5 : allFrom (shiftOk (ZMod 491) 121 plus minus) 122 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 153 to 183. -/
theorem shifts6 : allFrom (shiftOk (ZMod 491) 121 plus minus) 153 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 184 to 213. -/
theorem shifts7 : allFrom (shiftOk (ZMod 491) 121 plus minus) 184 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 214 to 244. -/
theorem shifts8 : allFrom (shiftOk (ZMod 491) 121 plus minus) 214 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 245 to 275. -/
theorem shifts9 : allFrom (shiftOk (ZMod 491) 121 plus minus) 245 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 276 to 305. -/
theorem shifts10 : allFrom (shiftOk (ZMod 491) 121 plus minus) 276 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 306 to 336. -/
theorem shifts11 : allFrom (shiftOk (ZMod 491) 121 plus minus) 306 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 337 to 367. -/
theorem shifts12 : allFrom (shiftOk (ZMod 491) 121 plus minus) 337 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 368 to 397. -/
theorem shifts13 : allFrom (shiftOk (ZMod 491) 121 plus minus) 368 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 398 to 428. -/
theorem shifts14 : allFrom (shiftOk (ZMod 491) 121 plus minus) 398 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 429 to 459. -/
theorem shifts15 : allFrom (shiftOk (ZMod 491) 121 plus minus) 429 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 460 to 490. -/
theorem shifts16 : allFrom (shiftOk (ZMod 491) 121 plus minus) 460 31 = true := by
  decide +kernel

theorem isSDS : IsSDS 246 121 sds := by
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
  have h := allFrom_append h shifts15
  have h := allFrom_append h shifts16
  exact isSDS_of_checkSplit count h

/-- N68249: C₄₉₁ has a signed difference set with
parameters (491, 246, 121). -/
theorem hasSDS :
    HasSDS (ZMod 491) 246 121 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N68249
