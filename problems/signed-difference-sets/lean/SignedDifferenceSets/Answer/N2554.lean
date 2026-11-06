module

public import SignedDifferenceSets.SetCheck

/-!
# N2554: a (111, 66, 17) SDS in C₁₁₁

Open in Gordon's table (`SDS(111,66,17,[111])`, 2026-11-05). The set is object O70
(`objects/O70.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N2554

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O70's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xedc534850f422bbd0d5ed35c48f

set_option linter.style.longLine false in
/-- Object O70's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x100004120c008000002200001200

/-- Object O70: the sign of each element. -/
def sds : ZMod 111 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 66 17 sds :=
  isSDS_of_checkSet (G := ZMod 111)
    (P := plus) (N := minus) (by decide +kernel)

/-- N2554: C₁₁₁ has a signed difference set with
parameters (111, 66, 17). -/
theorem hasSDS :
    HasSDS (ZMod 111) 66 17 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N2554
