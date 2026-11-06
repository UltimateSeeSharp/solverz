module

public import SignedDifferenceSets.SetCheck

/-!
# N742: a (64, 46, 30) SDS in C₄ × C₄ × C₄

Open in Gordon's table (`SDS(64,46,30,[4,4,4])`, 2026-11-05). The set is object O56
(`objects/O56.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N742

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O56's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x7fb6da7f7fece9e8

set_option linter.style.longLine false in
/-- Object O56's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O56: the sign of each element. -/
def sds : ZMod 4 × ZMod 4 × ZMod 4 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 46 30 sds :=
  isSDS_of_checkSet (G := ZMod 4 × ZMod 4 × ZMod 4)
    (P := plus) (N := minus) (by decide +kernel)

/-- N742: C₄ × C₄ × C₄ has a signed difference set with
parameters (64, 46, 30). -/
theorem hasSDS :
    HasSDS (ZMod 4 × ZMod 4 × ZMod 4) 46 30 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N742
