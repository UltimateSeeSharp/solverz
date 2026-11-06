module

public import SignedDifferenceSets.SetCheck

/-!
# N16957: a (256, 106, 42) SDS in C₁₆ × C₁₆

Open in Gordon's table (`SDS(256,106,42,[16,16])`, 2026-11-05). The set is object O31
(`objects/O31.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N16957

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O31's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xfc01a5a16493110118c7e1a12a55101154a90b0fc6310111924d0b4b007feeee

set_option linter.style.longLine false in
/-- Object O31's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O31: the sign of each element. -/
def sds : ZMod 16 × ZMod 16 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 106 42 sds :=
  isSDS_of_checkSet (G := ZMod 16 × ZMod 16) (P := plus) (N := minus) (by decide +kernel)

/-- N16957: C₁₆ × C₁₆ has a signed difference set with parameters (256, 106, 42). -/
theorem hasSDS : HasSDS (ZMod 16 × ZMod 16) 106 42 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N16957
