module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N6547: a (167, 84, 40) SDS in C₁₆₇

Open in Gordon's table (`SDS(167,84,40,[167])`, 2026-11-05). The set is object O85
(`objects/O85.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N6547

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O85's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O85's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x7bdab6ddca29e2e7e09c4dc6f818b86bac4492a420

/-- Object O85: the sign of each element. -/
def sds : ZMod 167 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 167) 84 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 40. -/
theorem shifts1 : allFrom (shiftOk (ZMod 167) 40 plus minus) 0 41 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 41 to 82. -/
theorem shifts2 : allFrom (shiftOk (ZMod 167) 40 plus minus) 41 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 83 to 124. -/
theorem shifts3 : allFrom (shiftOk (ZMod 167) 40 plus minus) 83 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 125 to 166. -/
theorem shifts4 : allFrom (shiftOk (ZMod 167) 40 plus minus) 125 42 = true := by
  decide +kernel

theorem isSDS : IsSDS 84 40 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N6547: C₁₆₇ has a signed difference set with
parameters (167, 84, 40). -/
theorem hasSDS :
    HasSDS (ZMod 167) 84 40 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N6547
