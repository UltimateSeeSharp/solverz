module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N7898: a (182, 101, 20) SDS in C₁₈₂

Open in Gordon's table (`SDS(182,101,20,[182])`, 2026-11-05). The set is object O68
(`objects/O68.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N7898

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O68's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1824b1e84cae0c429b1057ecfa29c2f66a3866ac94f4

set_option linter.style.longLine false in
/-- Object O68's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x800a0000000030880048081001400000000611000901

/-- Object O68: the sign of each element. -/
def sds : ZMod 182 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 182) 101 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 44. -/
theorem shifts1 : allFrom (shiftOk (ZMod 182) 20 plus minus) 0 45 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 45 to 90. -/
theorem shifts2 : allFrom (shiftOk (ZMod 182) 20 plus minus) 45 46 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 91 to 135. -/
theorem shifts3 : allFrom (shiftOk (ZMod 182) 20 plus minus) 91 45 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 136 to 181. -/
theorem shifts4 : allFrom (shiftOk (ZMod 182) 20 plus minus) 136 46 = true := by
  decide +kernel

theorem isSDS : IsSDS 101 20 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N7898: C₁₈₂ has a signed difference set with
parameters (182, 101, 20). -/
theorem hasSDS :
    HasSDS (ZMod 182) 101 20 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N7898
