module

public import SignedDifferenceSets.SetCheck

/-!
# N661: a (64, 18, 2) SDS in C₂ × C₂ × C₄ × C₄

Open in Gordon's table (`SDS(64,18,2,[2,2,4,4])`, 2026-11-05). The set is object O50
(`objects/O50.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N661

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O50's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1424442160000932

set_option linter.style.longLine false in
/-- Object O50's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0xa0004

/-- Object O50: the sign of each element. -/
def sds : ZMod 2 × ZMod 2 × ZMod 4 × ZMod 4 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 18 2 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 2 × ZMod 4 × ZMod 4)
    (P := plus) (N := minus) (by decide +kernel)

/-- N661: C₂ × C₂ × C₄ × C₄ has a signed difference set with
parameters (64, 18, 2). -/
theorem hasSDS :
    HasSDS (ZMod 2 × ZMod 2 × ZMod 4 × ZMod 4) 18 2 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N661
