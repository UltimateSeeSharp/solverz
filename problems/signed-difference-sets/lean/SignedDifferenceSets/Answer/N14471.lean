module

public import SignedDifferenceSets.SetCheck

/-!
# N14471: a (243, 82, 1) SDS in C₃ × C₃ × C₃ × C₃ × C₃

Open in Gordon's table (`SDS(243,82,1,[3,3,3,3,3])`, 2026-11-05). The set is object O102
(`objects/O102.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N14471

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O102's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x3ffb1d893f63b12793c9e01

set_option linter.style.longLine false in
/-- Object O102's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x4e276c09c4ed86c36000

/-- Object O102: the sign of each element. -/
def sds : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 82 1 sds :=
  isSDS_of_checkSet (G := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3)
    (P := plus) (N := minus) (by decide +kernel)

/-- N14471: C₃ × C₃ × C₃ × C₃ × C₃ has a signed difference set with
parameters (243, 82, 1). -/
theorem hasSDS :
    HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3) 82 1 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N14471
