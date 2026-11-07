module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N14597: a (243, 121, 40) SDS in C₃ × C₃ × C₃ × C₃ × C₃

Open in Gordon's table (`SDS(243,121,40,[3,3,3,3,3])`, 2026-11-05). The set is object O64
(`objects/O64.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 6 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N14597

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O64's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x2f08a8e0b2688cf0a961134f950dd03b993095b9955f4b760ce448203afc2

set_option linter.style.longLine false in
/-- Object O64's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x4000000042001020040000280000000400000000000000000021000000

/-- Object O64: the sign of each element. -/
def sds : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count :
    countOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 121 plus minus = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 39. -/
theorem shifts1 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 40 plus minus) 0 40 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 40 to 80. -/
theorem shifts2 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 40 plus minus) 40 41 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 81 to 120. -/
theorem shifts3 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 40 plus minus) 81 40 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 121 to 161. -/
theorem shifts4 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 40 plus minus) 121 41 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 162 to 201. -/
theorem shifts5 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 40 plus minus) 162 40 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 202 to 242. -/
theorem shifts6 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 40 plus minus) 202 41 =
      true := by
  decide +kernel

theorem isSDS : IsSDS 121 40 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  exact isSDS_of_checkSplit count h

/-- N14597: C₃ × C₃ × C₃ × C₃ × C₃ has a signed difference set with
parameters (243, 121, 40). -/
theorem hasSDS :
    HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 121 40 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N14597
