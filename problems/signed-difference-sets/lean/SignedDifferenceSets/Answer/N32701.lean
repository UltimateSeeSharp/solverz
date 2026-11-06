module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N32701: a (347, 174, 85) SDS in C₃₄₇

Open in Gordon's table (`SDS(347,174,85,[347])`, 2026-11-05). The set is object O88
(`objects/O88.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 12 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N32701

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O88's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O88's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x587e80577bbacc94917075671a5e7dcb7ce994afc1ccc7c0ad668c12c4185a71951f176d6cca22115fe81e4

/-- Object O88: the sign of each element. -/
def sds : ZMod 347 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 347) 174 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 27. -/
theorem shifts1 : allFrom (shiftOk (ZMod 347) 85 plus minus) 0 28 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 28 to 56. -/
theorem shifts2 : allFrom (shiftOk (ZMod 347) 85 plus minus) 28 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 57 to 85. -/
theorem shifts3 : allFrom (shiftOk (ZMod 347) 85 plus minus) 57 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 86 to 114. -/
theorem shifts4 : allFrom (shiftOk (ZMod 347) 85 plus minus) 86 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 115 to 143. -/
theorem shifts5 : allFrom (shiftOk (ZMod 347) 85 plus minus) 115 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 144 to 172. -/
theorem shifts6 : allFrom (shiftOk (ZMod 347) 85 plus minus) 144 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 173 to 201. -/
theorem shifts7 : allFrom (shiftOk (ZMod 347) 85 plus minus) 173 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 202 to 230. -/
theorem shifts8 : allFrom (shiftOk (ZMod 347) 85 plus minus) 202 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 231 to 259. -/
theorem shifts9 : allFrom (shiftOk (ZMod 347) 85 plus minus) 231 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 260 to 288. -/
theorem shifts10 : allFrom (shiftOk (ZMod 347) 85 plus minus) 260 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 289 to 317. -/
theorem shifts11 : allFrom (shiftOk (ZMod 347) 85 plus minus) 289 29 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 318 to 346. -/
theorem shifts12 : allFrom (shiftOk (ZMod 347) 85 plus minus) 318 29 = true := by
  decide +kernel

theorem isSDS : IsSDS 174 85 sds := by
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
  have h := allFrom_append h shifts11
  have h := allFrom_append h shifts12
  exact isSDS_of_checkSplit count h

/-- N32701: C₃₄₇ has a signed difference set with
parameters (347, 174, 85). -/
theorem hasSDS :
    HasSDS (ZMod 347) 174 85 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N32701
