module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N9609: a (199, 100, 48) SDS in C₁₉₉

Open in Gordon's table (`SDS(199,100,48,[199])`, 2026-11-05). The set is object O87
(`objects/O87.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N9609

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O87's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O87's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x6de6a96dd8977ce7e281c27a2ba1bc7eb818c116e4496a9848

/-- Object O87: the sign of each element. -/
def sds : ZMod 199 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 199) 100 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 48. -/
theorem shifts1 : allFrom (shiftOk (ZMod 199) 48 plus minus) 0 49 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 49 to 98. -/
theorem shifts2 : allFrom (shiftOk (ZMod 199) 48 plus minus) 49 50 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 99 to 148. -/
theorem shifts3 : allFrom (shiftOk (ZMod 199) 48 plus minus) 99 50 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 149 to 198. -/
theorem shifts4 : allFrom (shiftOk (ZMod 199) 48 plus minus) 149 50 = true := by
  decide +kernel

theorem isSDS : IsSDS 100 48 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N9609: C₁₉₉ has a signed difference set with
parameters (199, 100, 48). -/
theorem hasSDS :
    HasSDS (ZMod 199) 100 48 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N9609
