module

public import SignedDifferenceSets.SetCheck

/-!
# N933: a (72, 40, 4) SDS in C₃ × C₂₄

Open in Gordon's table (`SDS(72,40,4,[3,24])`, 2026-11-05). The set is object O82
(`objects/O82.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N933

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O82's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xcd4cd53d1180c11903

set_option linter.style.longLine false in
/-- Object O82's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x9008000251102410

/-- Object O82: the sign of each element. -/
def sds : ZMod 3 × ZMod 24 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 40 4 sds :=
  isSDS_of_checkSet (G := ZMod 3 × ZMod 24)
    (P := plus) (N := minus) (by decide +kernel)

/-- N933: C₃ × C₂₄ has a signed difference set with
parameters (72, 40, 4). -/
theorem hasSDS :
    HasSDS (ZMod 3 × ZMod 24) 40 4 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N933
