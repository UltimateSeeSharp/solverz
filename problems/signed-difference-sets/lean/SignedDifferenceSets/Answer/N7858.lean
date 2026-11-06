module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N7858: a (181, 136, 11) SDS in C₁₈₁

Open in Gordon's table (`SDS(181,136,11,[181])`, 2026-11-05). The set is object O93
(`objects/O93.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 6 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N7858

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O93's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1717e2151bcfb266b4947840878a4b59937cf62a11fa3b

set_option linter.style.longLine false in
/-- Object O93's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x6015a044300410482801075870b02464800154840444

/-- Object O93: the sign of each element. -/
def sds : ZMod 181 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 181) 136 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 29. -/
theorem shifts1 : allFrom (shiftOk (ZMod 181) 11 plus minus) 0 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 30 to 59. -/
theorem shifts2 : allFrom (shiftOk (ZMod 181) 11 plus minus) 30 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 60 to 89. -/
theorem shifts3 : allFrom (shiftOk (ZMod 181) 11 plus minus) 60 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 90 to 119. -/
theorem shifts4 : allFrom (shiftOk (ZMod 181) 11 plus minus) 90 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 120 to 149. -/
theorem shifts5 : allFrom (shiftOk (ZMod 181) 11 plus minus) 120 30 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 150 to 180. -/
theorem shifts6 : allFrom (shiftOk (ZMod 181) 11 plus minus) 150 31 = true := by
  decide +kernel

theorem isSDS : IsSDS 136 11 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  exact isSDS_of_checkSplit count h

/-- N7858: C₁₈₁ has a signed difference set with
parameters (181, 136, 11). -/
theorem hasSDS :
    HasSDS (ZMod 181) 136 11 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N7858
