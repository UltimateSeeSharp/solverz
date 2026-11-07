module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N14828: a (243, 177, 96) SDS in C₃ × C₃ × C₃ × C₃ × C₃

Open in Gordon's table (`SDS(243,177,96,[3,3,3,3,3])`, 2026-11-05). The set is object O65
(`objects/O65.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 8 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N14828

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O65's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x21000100000200802000000010040200000080000000001001

set_option linter.style.longLine false in
/-- Object O65's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x7afb7f3fcff143bec5bfbc9cf47cafedeeae6a9e5af7beb1f7bbbdcfe4ebc

/-- Object O65: the sign of each element. -/
def sds : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count :
    countOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 177 plus minus = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 29. -/
theorem shifts1 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 96 plus minus) 0 30 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 30 to 59. -/
theorem shifts2 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 96 plus minus) 30 30 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 60 to 90. -/
theorem shifts3 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 96 plus minus) 60 31 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 91 to 120. -/
theorem shifts4 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 96 plus minus) 91 30 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 121 to 150. -/
theorem shifts5 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 96 plus minus) 121 30 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 151 to 181. -/
theorem shifts6 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 96 plus minus) 151 31 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 182 to 211. -/
theorem shifts7 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 96 plus minus) 182 30 =
      true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 212 to 242. -/
theorem shifts8 :
    allFrom (shiftOk (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 96 plus minus) 212 31 =
      true := by
  decide +kernel

theorem isSDS : IsSDS 177 96 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  have h := allFrom_append h shifts7
  have h := allFrom_append h shifts8
  exact isSDS_of_checkSplit count h

/-- N14828: C₃ × C₃ × C₃ × C₃ × C₃ has a signed difference set with
parameters (243, 177, 96). -/
theorem hasSDS :
    HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 177 96 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N14828
