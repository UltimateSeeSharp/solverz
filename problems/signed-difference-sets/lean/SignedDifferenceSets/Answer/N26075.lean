module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N26075: a (312, 300, 200) SDS in C₃₁₂

Open in Gordon's table (`SDS(312,300,200,[312])`, 2026-11-05). The set is object O57
(`objects/O57.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 5 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N26075

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O57's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xfffdffbeeff7edf5bb7bffbffe7ffffd3ffdffeffffefaf3fffeeffffebfffffef7fe7fbffffee

set_option linter.style.longLine false in
/-- Object O57's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x200011008020a4480004000800002800200000001010c000010000100000000801800000010

/-- Object O57: the sign of each element. -/
def sds : ZMod 312 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 312) 300 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 61. -/
theorem shifts1 : allFrom (shiftOk (ZMod 312) 200 plus minus) 0 62 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 62 to 123. -/
theorem shifts2 : allFrom (shiftOk (ZMod 312) 200 plus minus) 62 62 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 124 to 186. -/
theorem shifts3 : allFrom (shiftOk (ZMod 312) 200 plus minus) 124 63 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 187 to 248. -/
theorem shifts4 : allFrom (shiftOk (ZMod 312) 200 plus minus) 187 62 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 249 to 311. -/
theorem shifts5 : allFrom (shiftOk (ZMod 312) 200 plus minus) 249 63 = true := by
  decide +kernel

theorem isSDS : IsSDS 300 200 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  exact isSDS_of_checkSplit count h

/-- N26075: C₃₁₂ has a signed difference set with
parameters (312, 300, 200). -/
theorem hasSDS :
    HasSDS (ZMod 312) 300 200 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N26075
