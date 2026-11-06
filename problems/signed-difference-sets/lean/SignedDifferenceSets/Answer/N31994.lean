module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N31994: a (343, 247, 51) SDS in C₇ × C₇ × C₇

Open in Gordon's table (`SDS(343,247,51,[7,7,7])`, 2026-11-05). The set is object O67
(`objects/O67.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 10 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N31994

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O67's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x3e385581b1ae855f8f428999cecadabf8693e45311f626d7a03fee3abcc3ebbef32452e6bbd7d9b9ed6396

set_option linter.style.longLine false in
/-- Object O67's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x850a3002112800208c0224201101402144022c020180081e001044000c04000451810104000044000800

/-- Object O67: the sign of each element. -/
def sds : ZMod 7 × ZMod 7 × ZMod 7 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 7 × ZMod 7 × ZMod 7) 247 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 33. -/
theorem shifts1 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 0 34 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 34 to 67. -/
theorem shifts2 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 34 34 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 68 to 101. -/
theorem shifts3 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 68 34 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 102 to 136. -/
theorem shifts4 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 102 35 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 137 to 170. -/
theorem shifts5 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 137 34 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 171 to 204. -/
theorem shifts6 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 171 34 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 205 to 239. -/
theorem shifts7 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 205 35 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 240 to 273. -/
theorem shifts8 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 240 34 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 274 to 307. -/
theorem shifts9 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 274 34 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 308 to 342. -/
theorem shifts10 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 51 plus minus) 308 35 = true := by
  decide +kernel

theorem isSDS : IsSDS 247 51 sds := by
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

/-- N31994: C₇ × C₇ × C₇ has a signed difference set with
parameters (343, 247, 51). -/
theorem hasSDS :
    HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 247 51 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N31994
