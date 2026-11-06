module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N47314: a (410, 329, 248) SDS in C₄₁₀

Open in Gordon's table (`SDS(410,329,248,[410])`, 2026-11-05). The set is object O58
(`objects/O58.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 7 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N47314

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O58's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x3d76cadefffbffeff75eafff4d7f43fbfdbc73fdf939bffb7fbb6efffbfbfcfbbfffbff3fd7cffe3efafffff7bf75db9de7fed6

set_option linter.style.longLine false in
/-- Object O58's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x10000000000000000000040000000000000000000100000000000000000000400000000000000000001

/-- Object O58: the sign of each element. -/
def sds : ZMod 410 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 410) 329 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 57. -/
theorem shifts1 : allFrom (shiftOk (ZMod 410) 248 plus minus) 0 58 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 58 to 116. -/
theorem shifts2 : allFrom (shiftOk (ZMod 410) 248 plus minus) 58 59 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 117 to 174. -/
theorem shifts3 : allFrom (shiftOk (ZMod 410) 248 plus minus) 117 58 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 175 to 233. -/
theorem shifts4 : allFrom (shiftOk (ZMod 410) 248 plus minus) 175 59 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 234 to 291. -/
theorem shifts5 : allFrom (shiftOk (ZMod 410) 248 plus minus) 234 58 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 292 to 350. -/
theorem shifts6 : allFrom (shiftOk (ZMod 410) 248 plus minus) 292 59 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 351 to 409. -/
theorem shifts7 : allFrom (shiftOk (ZMod 410) 248 plus minus) 351 59 = true := by
  decide +kernel

theorem isSDS : IsSDS 329 248 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  have h := allFrom_append h shifts7
  exact isSDS_of_checkSplit count h

/-- N47314: C₄₁₀ has a signed difference set with
parameters (410, 329, 248). -/
theorem hasSDS :
    HasSDS (ZMod 410) 329 248 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N47314
