module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N18527: a (263, 132, 64) SDS in C₂₆₃

Open in Gordon's table (`SDS(263,132,64,[263])`, 2026-11-05). The set is object O77
(`objects/O77.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N18527

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O77's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x7adce3f1fd1afa06aeb252cdbbcd0468cce9df4c224cb5b28a9fa0a7407038c4a0

set_option linter.style.longLine false in
/-- Object O77's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O77: the sign of each element. -/
def sds : ZMod 263 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 263) 132 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 64. -/
theorem shifts1 : allFrom (shiftOk (ZMod 263) 64 plus minus) 0 65 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 65 to 130. -/
theorem shifts2 : allFrom (shiftOk (ZMod 263) 64 plus minus) 65 66 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 131 to 196. -/
theorem shifts3 : allFrom (shiftOk (ZMod 263) 64 plus minus) 131 66 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 197 to 262. -/
theorem shifts4 : allFrom (shiftOk (ZMod 263) 64 plus minus) 197 66 = true := by
  decide +kernel

theorem isSDS : IsSDS 132 64 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N18527: C₂₆₃ has a signed difference set with
parameters (263, 132, 64). -/
theorem hasSDS :
    HasSDS (ZMod 263) 132 64 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N18527
