module

public import SignedDifferenceSets.SetCheck

/-!
# N3243: a (125, 28, 3) SDS in C₅ × C₂₅

Open in Gordon's table (`SDS(125,28,3,[5,25])`, 2026-11-05). The set is object O40
(`objects/O40.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N3243

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O40's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x22220140a040920240608208200001e

set_option linter.style.longLine false in
/-- Object O40's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x108420

/-- Object O40: the sign of each element. -/
def sds : ZMod 5 × ZMod 25 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 28 3 sds :=
  isSDS_of_checkSet (G := ZMod 5 × ZMod 25)
    (P := plus) (N := minus) (by decide +kernel)

/-- N3243: C₅ × C₂₅ has a signed difference set with
parameters (125, 28, 3). -/
theorem hasSDS :
    HasSDS (ZMod 5 × ZMod 25) 28 3 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N3243
