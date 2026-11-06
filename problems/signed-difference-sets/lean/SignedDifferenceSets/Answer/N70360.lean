module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N70360: a (499, 250, 123) SDS in C₄₉₉

Open in Gordon's table (`SDS(499,250,123,[499])`, 2026-11-05). The set is object O92
(`objects/O92.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 16 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N70360

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O92's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O92's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x4e428ee76b1752c09664e8908df70bff3cd3c39b476a6dbe3f085584fa750555f51a0de55ef038249a91d263c34c3002f104ef6e8d996fcb51729188ebd8c

/-- Object O92: the sign of each element. -/
def sds : ZMod 499 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 499) 250 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 30. -/
theorem shifts1 : allFrom (shiftOk (ZMod 499) 123 plus minus) 0 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 31 to 61. -/
theorem shifts2 : allFrom (shiftOk (ZMod 499) 123 plus minus) 31 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 62 to 92. -/
theorem shifts3 : allFrom (shiftOk (ZMod 499) 123 plus minus) 62 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 93 to 123. -/
theorem shifts4 : allFrom (shiftOk (ZMod 499) 123 plus minus) 93 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 124 to 154. -/
theorem shifts5 : allFrom (shiftOk (ZMod 499) 123 plus minus) 124 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 155 to 186. -/
theorem shifts6 : allFrom (shiftOk (ZMod 499) 123 plus minus) 155 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 187 to 217. -/
theorem shifts7 : allFrom (shiftOk (ZMod 499) 123 plus minus) 187 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 218 to 248. -/
theorem shifts8 : allFrom (shiftOk (ZMod 499) 123 plus minus) 218 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 249 to 279. -/
theorem shifts9 : allFrom (shiftOk (ZMod 499) 123 plus minus) 249 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 280 to 310. -/
theorem shifts10 : allFrom (shiftOk (ZMod 499) 123 plus minus) 280 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 311 to 342. -/
theorem shifts11 : allFrom (shiftOk (ZMod 499) 123 plus minus) 311 32 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 343 to 373. -/
theorem shifts12 : allFrom (shiftOk (ZMod 499) 123 plus minus) 343 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 374 to 404. -/
theorem shifts13 : allFrom (shiftOk (ZMod 499) 123 plus minus) 374 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 405 to 435. -/
theorem shifts14 : allFrom (shiftOk (ZMod 499) 123 plus minus) 405 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 436 to 466. -/
theorem shifts15 : allFrom (shiftOk (ZMod 499) 123 plus minus) 436 31 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 467 to 498. -/
theorem shifts16 : allFrom (shiftOk (ZMod 499) 123 plus minus) 467 32 = true := by
  decide +kernel

theorem isSDS : IsSDS 250 123 sds := by
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

/-- N70360: C₄₉₉ has a signed difference set with
parameters (499, 250, 123). -/
theorem hasSDS :
    HasSDS (ZMod 499) 250 123 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N70360
