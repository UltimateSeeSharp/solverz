module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N12056: a (223, 112, 54) SDS in C₂₂₃

Open in Gordon's table (`SDS(223,112,54,[223])`, 2026-11-05). The set is object O75
(`objects/O75.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N12056

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O75's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x69c3f04fef5165abecea72422c6699cbbdb1a8c82a5975080df03c68

set_option linter.style.longLine false in
/-- Object O75's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O75: the sign of each element. -/
def sds : ZMod 223 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 223) 112 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 54. -/
theorem shifts1 : allFrom (shiftOk (ZMod 223) 54 plus minus) 0 55 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 55 to 110. -/
theorem shifts2 : allFrom (shiftOk (ZMod 223) 54 plus minus) 55 56 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 111 to 166. -/
theorem shifts3 : allFrom (shiftOk (ZMod 223) 54 plus minus) 111 56 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 167 to 222. -/
theorem shifts4 : allFrom (shiftOk (ZMod 223) 54 plus minus) 167 56 = true := by
  decide +kernel

theorem isSDS : IsSDS 112 54 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N12056: C₂₂₃ has a signed difference set with
parameters (223, 112, 54). -/
theorem hasSDS :
    HasSDS (ZMod 223) 112 54 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N12056
