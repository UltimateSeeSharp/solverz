module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N49190: a (419, 210, 103) SDS in C₄₁₉

Open in Gordon's table (`SDS(419,210,103,[419])`, 2026-11-05). The set is object O74
(`objects/O74.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 8 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N49190

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O74's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O74's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x22b270a3c0aa37e41bae3667b584438bac212253b592978060c83ecf9fe16b65235bb7bca2e3dde5219938a27d813aafc3af1b2ba

/-- Object O74: the sign of each element. -/
def sds : ZMod 419 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 419) 210 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 51. -/
theorem shifts1 : allFrom (shiftOk (ZMod 419) 103 plus minus) 0 52 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 52 to 103. -/
theorem shifts2 : allFrom (shiftOk (ZMod 419) 103 plus minus) 52 52 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 104 to 156. -/
theorem shifts3 : allFrom (shiftOk (ZMod 419) 103 plus minus) 104 53 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 157 to 208. -/
theorem shifts4 : allFrom (shiftOk (ZMod 419) 103 plus minus) 157 52 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 209 to 260. -/
theorem shifts5 : allFrom (shiftOk (ZMod 419) 103 plus minus) 209 52 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 261 to 313. -/
theorem shifts6 : allFrom (shiftOk (ZMod 419) 103 plus minus) 261 53 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 314 to 365. -/
theorem shifts7 : allFrom (shiftOk (ZMod 419) 103 plus minus) 314 52 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 366 to 418. -/
theorem shifts8 : allFrom (shiftOk (ZMod 419) 103 plus minus) 366 53 = true := by
  decide +kernel

theorem isSDS : IsSDS 210 103 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  have h := allFrom_append h shifts7
  have h := allFrom_append h shifts8
  exact isSDS_of_checkSplit count h

/-- N49190: C₄₁₉ has a signed difference set with
parameters (419, 210, 103). -/
theorem hasSDS :
    HasSDS (ZMod 419) 210 103 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N49190
