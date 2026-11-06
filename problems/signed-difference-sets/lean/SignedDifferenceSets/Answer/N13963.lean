module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N13963: a (239, 120, 58) SDS in C₂₃₉

Open in Gordon's table (`SDS(239,120,58,[239])`, 2026-11-05). The set is object O76
(`objects/O76.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N13963

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O76's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x7ef9ead7e88cf32eb990d5b4be0e48ed8f82d254f6628b30cee814a86080

set_option linter.style.longLine false in
/-- Object O76's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O76: the sign of each element. -/
def sds : ZMod 239 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 239) 120 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 58. -/
theorem shifts1 : allFrom (shiftOk (ZMod 239) 58 plus minus) 0 59 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 59 to 118. -/
theorem shifts2 : allFrom (shiftOk (ZMod 239) 58 plus minus) 59 60 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 119 to 178. -/
theorem shifts3 : allFrom (shiftOk (ZMod 239) 58 plus minus) 119 60 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 179 to 238. -/
theorem shifts4 : allFrom (shiftOk (ZMod 239) 58 plus minus) 179 60 = true := by
  decide +kernel

theorem isSDS : IsSDS 120 58 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N13963: C₂₃₉ has a signed difference set with
parameters (239, 120, 58). -/
theorem hasSDS :
    HasSDS (ZMod 239) 120 58 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N13963
