module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N16190: a (251, 126, 61) SDS in C₂₅₁

Open in Gordon's table (`SDS(251,126,61,[251])`, 2026-11-05). The set is object O72
(`objects/O72.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N16190

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O72's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1

set_option linter.style.longLine false in
/-- Object O72's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x5d4dcf591b44d829fc71dede0d6af77c110a94f848471c06be4dd27650c4d44

/-- Object O72: the sign of each element. -/
def sds : ZMod 251 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 251) 126 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 61. -/
theorem shifts1 : allFrom (shiftOk (ZMod 251) 61 plus minus) 0 62 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 62 to 124. -/
theorem shifts2 : allFrom (shiftOk (ZMod 251) 61 plus minus) 62 63 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 125 to 187. -/
theorem shifts3 : allFrom (shiftOk (ZMod 251) 61 plus minus) 125 63 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 188 to 250. -/
theorem shifts4 : allFrom (shiftOk (ZMod 251) 61 plus minus) 188 63 = true := by
  decide +kernel

theorem isSDS : IsSDS 126 61 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N16190: C₂₅₁ has a signed difference set with
parameters (251, 126, 61). -/
theorem hasSDS :
    HasSDS (ZMod 251) 126 61 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N16190
