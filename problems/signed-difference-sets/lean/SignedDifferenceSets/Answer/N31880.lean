module

public import SignedDifferenceSets.SetCheckSplit

/-!
# N31880: a (343, 199, 3) SDS in C₇ × C₇ × C₇

Open in Gordon's table (`SDS(343,199,3,[7,7,7])`, 2026-11-05). The set is object O66
(`objects/O66.txt`); this file is generated from it by `solver/answer.py`, its shifts
checked in 8 ranges.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N31880

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O66's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x4414148320024900a2012200a1840000930281842021844044014b00820400480828e2009338545439969

set_option linter.style.longLine false in
/-- Object O66's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x5b081a8084a351678040c94a3404151e208dc04321bd24811a0661460740baaa28100193e4cc782aa40200

/-- Object O66: the sign of each element. -/
def sds : ZMod 7 × ZMod 7 × ZMod 7 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
theorem count : countOk (ZMod 7 × ZMod 7 × ZMod 7) 199 plus minus = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 0 to 41. -/
theorem shifts1 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 3 plus minus) 0 42 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 42 to 84. -/
theorem shifts2 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 3 plus minus) 42 43 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 85 to 127. -/
theorem shifts3 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 3 plus minus) 85 43 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 128 to 170. -/
theorem shifts4 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 3 plus minus) 128 43 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 171 to 213. -/
theorem shifts5 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 3 plus minus) 171 43 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 214 to 256. -/
theorem shifts6 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 3 plus minus) 214 43 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 257 to 299. -/
theorem shifts7 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 3 plus minus) 257 43 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Shifts 300 to 342. -/
theorem shifts8 : allFrom (shiftOk (ZMod 7 × ZMod 7 × ZMod 7) 3 plus minus) 300 43 = true := by
  decide +kernel

theorem isSDS : IsSDS 199 3 sds := by
  have h := shifts1
  have h := allFrom_append h shifts2
  have h := allFrom_append h shifts3
  have h := allFrom_append h shifts4
  have h := allFrom_append h shifts5
  have h := allFrom_append h shifts6
  have h := allFrom_append h shifts7
  have h := allFrom_append h shifts8
  exact isSDS_of_checkSplit count h

/-- N31880: C₇ × C₇ × C₇ has a signed difference set with
parameters (343, 199, 3). -/
theorem hasSDS :
    HasSDS (ZMod 7 × ZMod 7 × ZMod 7) 199 3 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N31880
