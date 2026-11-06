module

public import SignedDifferenceSets.SetCheck

/-!
# N11650: a (217, 193, 168) SDS in C₂₁₇

Open in Gordon's table (`SDS(217,193,168,[217])`, 2026-11-05). The set is object O36
(`objects/O36.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N11650

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O36's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1dfffdbefff7de5fb7f7fffff5ffe3fffbdeefefffffff7ffffff7e

set_option linter.style.longLine false in
/-- Object O36's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O36: the sign of each element. -/
def sds : ZMod 217 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 193 168 sds :=
  isSDS_of_checkSet (G := ZMod 217)
    (P := plus) (N := minus) (by decide +kernel)

/-- N11650: C₂₁₇ has a signed difference set with
parameters (217, 193, 168). -/
theorem hasSDS :
    HasSDS (ZMod 217) 193 168 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N11650
