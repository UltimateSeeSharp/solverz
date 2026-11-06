module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N11602: a (217, 112, 12) SDS in C₂₁₇

Open in Gordon's table (`SDS(217,112,12,[217])`, 2026-11-05). The set is object O63
(`objects/O63.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N11602

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O63's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xa48ae0276505820cdc22009cb857092b58a21276f14c24c0e03841

set_option linter.style.longLine false in
/-- Object O63's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1130001000a1040420209840104000010200c00000010002d028008

/-- Object O63: the sign of each element. -/
def sds : ZMod 217 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 217) 112 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 53. -/
theorem shifts1 : allFrom (shiftOk (ZMod 217) 12 plus minus) 0 54 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 54 to 107. -/
theorem shifts2 : allFrom (shiftOk (ZMod 217) 12 plus minus) 54 54 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 108 to 161. -/
theorem shifts3 : allFrom (shiftOk (ZMod 217) 12 plus minus) 108 54 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 162 to 216. -/
theorem shifts4 : allFrom (shiftOk (ZMod 217) 12 plus minus) 162 55 = true := by
  decide +kernel

theorem isSDS : IsSDS 112 12 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N11602: C₂₁₇ has a signed difference set with
parameters (217, 112, 12). -/
theorem hasSDS :
    HasSDS (ZMod 217) 112 12 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N11602
