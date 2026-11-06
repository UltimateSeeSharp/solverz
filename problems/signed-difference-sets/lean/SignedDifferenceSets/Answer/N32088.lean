module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N32088: a (343, 289, 240) SDS in C₇ × C₄₉

Open in Gordon's table (`SDS(343,289,240,[7,49])`, 2026-11-05). The set is object O46
(`objects/O46.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 6 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N32088

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O46's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x7df7df7df7ffb7fdbfedff7fd7fbfd7fbfdfef7bdffdef7ff777feeffddff9fdfdfdfdfdfdfbf7efdfbf00

set_option linter.style.longLine false in
/-- Object O46's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O46: the sign of each element. -/
def sds : ZMod 7 × ZMod 49 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 7 × ZMod 49) 289 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 56. -/
theorem shifts1 : allFrom (shiftOk (ZMod 7 × ZMod 49) 240 plus minus) 0 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 57 to 113. -/
theorem shifts2 : allFrom (shiftOk (ZMod 7 × ZMod 49) 240 plus minus) 57 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 114 to 170. -/
theorem shifts3 : allFrom (shiftOk (ZMod 7 × ZMod 49) 240 plus minus) 114 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 171 to 227. -/
theorem shifts4 : allFrom (shiftOk (ZMod 7 × ZMod 49) 240 plus minus) 171 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 228 to 284. -/
theorem shifts5 : allFrom (shiftOk (ZMod 7 × ZMod 49) 240 plus minus) 228 57 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 285 to 342. -/
theorem shifts6 : allFrom (shiftOk (ZMod 7 × ZMod 49) 240 plus minus) 285 58 = true := by
  decide +kernel

theorem isSDS : IsSDS 289 240 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  exact isSDS_of_checkSplit count h

/-- N32088: C₇ × C₄₉ has a signed difference set with
parameters (343, 289, 240). -/
theorem hasSDS :
    HasSDS (ZMod 7 × ZMod 49) 289 240 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N32088
