module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N15663: a (247, 127, 63) SDS in C₂₄₇

Open in Gordon's table (`SDS(247,127,63,[247])`, 2026-11-05). The set is object O99
(`objects/O99.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 6 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N15663

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O99's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x7acda5b389628b0ed0867d5c858e05fcb351812c2fe323e5d12391bd1577fe

set_option linter.style.longLine false in
/-- Object O99's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O99: the sign of each element. -/
def sds : ZMod 247 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 247) 127 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 40. -/
theorem shifts1 : allFrom (shiftOk (ZMod 247) 63 plus minus) 0 41 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 41 to 81. -/
theorem shifts2 : allFrom (shiftOk (ZMod 247) 63 plus minus) 41 41 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 82 to 122. -/
theorem shifts3 : allFrom (shiftOk (ZMod 247) 63 plus minus) 82 41 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 123 to 163. -/
theorem shifts4 : allFrom (shiftOk (ZMod 247) 63 plus minus) 123 41 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 164 to 204. -/
theorem shifts5 : allFrom (shiftOk (ZMod 247) 63 plus minus) 164 41 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 205 to 246. -/
theorem shifts6 : allFrom (shiftOk (ZMod 247) 63 plus minus) 205 42 = true := by
  decide +kernel

theorem isSDS : IsSDS 127 63 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  exact isSDS_of_checkSplit count h

/-- N15663: C₂₄₇ has a signed difference set with
parameters (247, 127, 63). -/
theorem hasSDS :
    HasSDS (ZMod 247) 127 63 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N15663
