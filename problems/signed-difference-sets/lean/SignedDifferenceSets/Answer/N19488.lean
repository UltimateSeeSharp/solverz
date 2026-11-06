module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N19488: a (271, 136, 66) SDS in C₂₇₁

Open in Gordon's table (`SDS(271,136,66,[271])`, 2026-11-05). The set is object O73
(`objects/O73.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N19488

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O73's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O73's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x6df2ea49bdcc65c79ea7f5e03922a16ec2bc897abb63f8501a861c59cc426da8b048

/-- Object O73: the sign of each element. -/
def sds : ZMod 271 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 271) 136 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 66. -/
theorem shifts1 : allFrom (shiftOk (ZMod 271) 66 plus minus) 0 67 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 67 to 134. -/
theorem shifts2 : allFrom (shiftOk (ZMod 271) 66 plus minus) 67 68 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 135 to 202. -/
theorem shifts3 : allFrom (shiftOk (ZMod 271) 66 plus minus) 135 68 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 203 to 270. -/
theorem shifts4 : allFrom (shiftOk (ZMod 271) 66 plus minus) 203 68 = true := by
  decide +kernel

theorem isSDS : IsSDS 136 66 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N19488: C₂₇₁ has a signed difference set with
parameters (271, 136, 66). -/
theorem hasSDS :
    HasSDS (ZMod 271) 136 66 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N19488
