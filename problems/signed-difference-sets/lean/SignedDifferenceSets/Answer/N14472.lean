module

public import SignedDifferenceSets.SetCheck

/-!
# N14472: a (243, 82, 1) SDS in C₃ × C₃ × C₃ × C₉

Open in Gordon's table (`SDS(243,82,1,[3,3,3,9])`, 2026-11-05). The set is object O103
(`objects/O103.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N14472

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O103's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x120900124120020100924904800920900100804920201128040225128944b

set_option linter.style.longLine false in
/-- Object O103's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x40248008049048240000201240040248241200048240009048000000000

/-- Object O103: the sign of each element. -/
def sds : ZMod 3 × ZMod 3 × ZMod 3 × ZMod 9 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 82 1 sds :=
  isSDS_of_checkSet (G := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 9)
    (P := plus) (N := minus) (by decide +kernel)

/-- N14472: C₃ × C₃ × C₃ × C₉ has a signed difference set with
parameters (243, 82, 1). -/
theorem hasSDS :
    HasSDS (ZMod 3 × ZMod 3 × ZMod 3 × ZMod 9) 82 1 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N14472
