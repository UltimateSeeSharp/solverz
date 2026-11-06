module

public import SignedDifferenceSets.SetCheck

/-!
# N3314: a (125, 97, 72) SDS in C₅ × C₅ × C₅

Open in Gordon's table (`SDS(125,97,72,[5,5,5])`, 2026-11-05). The set is object O43
(`objects/O43.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N3314

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O43's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1ddddfedbfb7f5fafdf9f7df7def7bc0

set_option linter.style.longLine false in
/-- Object O43's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O43: the sign of each element. -/
def sds : ZMod 5 × ZMod 5 × ZMod 5 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 97 72 sds :=
  isSDS_of_checkSet (G := ZMod 5 × ZMod 5 × ZMod 5)
    (P := plus) (N := minus) (by decide +kernel)

/-- N3314: C₅ × C₅ × C₅ has a signed difference set with
parameters (125, 97, 72). -/
theorem hasSDS :
    HasSDS (ZMod 5 × ZMod 5 × ZMod 5) 97 72 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N3314
