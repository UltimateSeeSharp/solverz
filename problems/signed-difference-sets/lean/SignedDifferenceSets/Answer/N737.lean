module

public import SignedDifferenceSets.SetCheck

/-!
# N737: a (64, 46, 30) SDS in C₂ × C₂ × C₂ × C₈

Open in Gordon's table (`SDS(64,46,30,[2,2,2,8])`, 2026-11-05). The set is object O54
(`objects/O54.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N737

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O54's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xdb7ed7eb7bedeee0

set_option linter.style.longLine false in
/-- Object O54's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O54: the sign of each element. -/
def sds : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 8 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 46 30 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 8)
    (P := plus) (N := minus) (by decide +kernel)

/-- N737: C₂ × C₂ × C₂ × C₈ has a signed difference set with
parameters (64, 46, 30). -/
theorem hasSDS :
    HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 8) 46 30 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N737
