module

public import SignedDifferenceSets.SetCheck

/-!
# N448: a (54, 38, 2) SDS in C₃ × C₃ × C₆

Open in Gordon's table (`SDS(54,38,2,[3,3,6])`, 2026-11-05). The set is object O79
(`objects/O79.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N448

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O79's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x3fb426c10481dd

set_option linter.style.longLine false in
/-- Object O79's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x490908201e22

/-- Object O79: the sign of each element. -/
def sds : ZMod 3 × ZMod 3 × ZMod 6 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 38 2 sds :=
  isSDS_of_checkSet (G := ZMod 3 × ZMod 3 × ZMod 6)
    (P := plus) (N := minus) (by decide +kernel)

/-- N448: C₃ × C₃ × C₆ has a signed difference set with
parameters (54, 38, 2). -/
theorem hasSDS :
    HasSDS (ZMod 3 × ZMod 3 × ZMod 6) 38 2 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N448
