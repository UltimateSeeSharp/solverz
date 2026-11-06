module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N2215: a (104, 29, 4) SDS in C₁₀₄

Open in Gordon's table (`SDS(104,29,4,[104])`, 2026-11-05). The set is object O98
(`objects/O98.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N2215

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O98's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x100205811800061105262836a

set_option linter.style.longLine false in
/-- Object O98's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x80000020000008000002000

/-- Object O98: the sign of each element. -/
def sds : ZMod 104 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 104) 29 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 25. -/
theorem shifts1 : allFrom (shiftOk (ZMod 104) 4 plus minus) 0 26 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 26 to 51. -/
theorem shifts2 : allFrom (shiftOk (ZMod 104) 4 plus minus) 26 26 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 52 to 77. -/
theorem shifts3 : allFrom (shiftOk (ZMod 104) 4 plus minus) 52 26 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 78 to 103. -/
theorem shifts4 : allFrom (shiftOk (ZMod 104) 4 plus minus) 78 26 = true := by
  decide +kernel

theorem isSDS : IsSDS 29 4 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N2215: C₁₀₄ has a signed difference set with
parameters (104, 29, 4). -/
theorem hasSDS :
    HasSDS (ZMod 104) 29 4 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N2215
