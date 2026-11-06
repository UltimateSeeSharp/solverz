module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N49624: a (421, 316, 25) SDS in C₄₂₁

Open in Gordon's table (`SDS(421,316,25,[421])`, 2026-11-05). The set is object O78
(`objects/O78.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 10 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N49624

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O78's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x8a98ce1a97c4bb599f2047e6880c724f1b152cbfa2f145a1dadffed6e168a3d17f4d2a363c938c0459f8813e66b748fa561cc6544

set_option linter.style.longLine false in
/-- Object O78's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x34251000283044864092080832a38030e42881401d0c8a52210001080c031000801290c0006c02a8a2036c8101003400a9e110a0b

/-- Object O78: the sign of each element. -/
def sds : ZMod 421 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 421) 316 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 41. -/
theorem shifts1 : allFrom (shiftOk (ZMod 421) 25 plus minus) 0 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 42 to 83. -/
theorem shifts2 : allFrom (shiftOk (ZMod 421) 25 plus minus) 42 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 84 to 125. -/
theorem shifts3 : allFrom (shiftOk (ZMod 421) 25 plus minus) 84 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 126 to 167. -/
theorem shifts4 : allFrom (shiftOk (ZMod 421) 25 plus minus) 126 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 168 to 209. -/
theorem shifts5 : allFrom (shiftOk (ZMod 421) 25 plus minus) 168 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 210 to 251. -/
theorem shifts6 : allFrom (shiftOk (ZMod 421) 25 plus minus) 210 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 252 to 293. -/
theorem shifts7 : allFrom (shiftOk (ZMod 421) 25 plus minus) 252 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 294 to 335. -/
theorem shifts8 : allFrom (shiftOk (ZMod 421) 25 plus minus) 294 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 336 to 377. -/
theorem shifts9 : allFrom (shiftOk (ZMod 421) 25 plus minus) 336 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 378 to 420. -/
theorem shifts10 : allFrom (shiftOk (ZMod 421) 25 plus minus) 378 43 = true := by
  decide +kernel

theorem isSDS : IsSDS 316 25 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  have h := allFrom_append h shifts7
  have h := allFrom_append h shifts8
  have h := allFrom_append h shifts9
  have h := allFrom_append h shifts10
  exact isSDS_of_checkSplit count h

/-- N49624: C₄₂₁ has a signed difference set with
parameters (421, 316, 25). -/
theorem hasSDS :
    HasSDS (ZMod 421) 316 25 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N49624
