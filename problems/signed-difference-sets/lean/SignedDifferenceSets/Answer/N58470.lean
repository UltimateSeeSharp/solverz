module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N58470: a (455, 71, 7) SDS in C₄₅₅

Open in Gordon's table (`SDS(455,71,7,[455])`, 2026-11-05). The set is object O38
(`objects/O38.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 8 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N58470

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O38's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1000010600000005120428000101100000002202080121088050004012000342001140000001100c0840180580014208430180910536

set_option linter.style.longLine false in
/-- Object O38's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x40000000000000002000000000000000100000000000000008000000000000000400000000000000020000000000000001

/-- Object O38: the sign of each element. -/
def sds : ZMod 455 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 455) 71 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 55. -/
theorem shifts1 : allFrom (shiftOk (ZMod 455) 7 plus minus) 0 56 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 56 to 112. -/
theorem shifts2 : allFrom (shiftOk (ZMod 455) 7 plus minus) 56 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 113 to 169. -/
theorem shifts3 : allFrom (shiftOk (ZMod 455) 7 plus minus) 113 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 170 to 226. -/
theorem shifts4 : allFrom (shiftOk (ZMod 455) 7 plus minus) 170 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 227 to 283. -/
theorem shifts5 : allFrom (shiftOk (ZMod 455) 7 plus minus) 227 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 284 to 340. -/
theorem shifts6 : allFrom (shiftOk (ZMod 455) 7 plus minus) 284 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 341 to 397. -/
theorem shifts7 : allFrom (shiftOk (ZMod 455) 7 plus minus) 341 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 398 to 454. -/
theorem shifts8 : allFrom (shiftOk (ZMod 455) 7 plus minus) 398 57 = true := by
  decide +kernel

theorem isSDS : IsSDS 71 7 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  have h := allFrom_append h shifts7
  have h := allFrom_append h shifts8
  exact isSDS_of_checkSplit count h

/-- N58470: C₄₅₅ has a signed difference set with
parameters (455, 71, 7). -/
theorem hasSDS :
    HasSDS (ZMod 455) 71 7 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N58470
