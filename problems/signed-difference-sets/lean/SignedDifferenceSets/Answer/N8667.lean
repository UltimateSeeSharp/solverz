module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N8667: a (191, 96, 46) SDS in C₁₉₁

Open in Gordon's table (`SDS(191,96,46,[191])`, 2026-11-05). The set is object O86
(`objects/O86.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N8667

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O86's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O86's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x7eede9f2a996fa18dc97c628eb9c16c4e7a0966ab0684880

/-- Object O86: the sign of each element. -/
def sds : ZMod 191 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 191) 96 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 46. -/
theorem shifts1 : allFrom (shiftOk (ZMod 191) 46 plus minus) 0 47 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 47 to 94. -/
theorem shifts2 : allFrom (shiftOk (ZMod 191) 46 plus minus) 47 48 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 95 to 142. -/
theorem shifts3 : allFrom (shiftOk (ZMod 191) 46 plus minus) 95 48 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 143 to 190. -/
theorem shifts4 : allFrom (shiftOk (ZMod 191) 46 plus minus) 143 48 = true := by
  decide +kernel

theorem isSDS : IsSDS 96 46 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N8667: C₁₉₁ has a signed difference set with
parameters (191, 96, 46). -/
theorem hasSDS :
    HasSDS (ZMod 191) 96 46 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N8667
