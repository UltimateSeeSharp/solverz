module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N9807: a (200, 151, 102) SDS in C₂₀₀

Open in Gordon's table (`SDS(200,151,102,[200])`, 2026-11-05). The set is object O60
(`objects/O60.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 4 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N9807

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O60's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xff57f2d7f75f8eeffffb67fe4e5fa3dfb78a6b7bb73cfbbffe

set_option linter.style.longLine false in
/-- Object O60's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x40000000000010000000000004000000000001

/-- Object O60: the sign of each element. -/
def sds : ZMod 200 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 200) 151 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 49. -/
theorem shifts1 : allFrom (shiftOk (ZMod 200) 102 plus minus) 0 50 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 50 to 99. -/
theorem shifts2 : allFrom (shiftOk (ZMod 200) 102 plus minus) 50 50 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 100 to 149. -/
theorem shifts3 : allFrom (shiftOk (ZMod 200) 102 plus minus) 100 50 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 150 to 199. -/
theorem shifts4 : allFrom (shiftOk (ZMod 200) 102 plus minus) 150 50 = true := by
  decide +kernel

theorem isSDS : IsSDS 151 102 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  exact isSDS_of_checkSplit count h

/-- N9807: C₂₀₀ has a signed difference set with
parameters (200, 151, 102). -/
theorem hasSDS :
    HasSDS (ZMod 200) 151 102 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N9807
