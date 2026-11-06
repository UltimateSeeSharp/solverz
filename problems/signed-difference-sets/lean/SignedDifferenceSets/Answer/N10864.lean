module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N10864: a (211, 106, 51) SDS in C₂₁₁

Open in Gordon's table (`SDS(211,106,51,[211])`, 2026-11-05). The set is object O71
(`objects/O71.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N10864

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O71's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O71's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x31a9633dd3e0a04d18b406fa62ab9a09fd2e74dfaf83443396a72

/-- Object O71: the sign of each element. -/
def sds : ZMod 211 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 211) 106 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 51. -/
theorem shifts1 : allFrom (shiftOk (ZMod 211) 51 plus minus) 0 52 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 52 to 104. -/
theorem shifts2 : allFrom (shiftOk (ZMod 211) 51 plus minus) 52 53 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 105 to 157. -/
theorem shifts3 : allFrom (shiftOk (ZMod 211) 51 plus minus) 105 53 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 158 to 210. -/
theorem shifts4 : allFrom (shiftOk (ZMod 211) 51 plus minus) 158 53 = true := by
  decide +kernel

theorem isSDS : IsSDS 106 51 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N10864: C₂₁₁ has a signed difference set with
parameters (211, 106, 51). -/
theorem hasSDS :
    HasSDS (ZMod 211) 106 51 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N10864
