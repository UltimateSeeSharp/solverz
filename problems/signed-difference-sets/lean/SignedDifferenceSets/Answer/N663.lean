module

public import SignedDifferenceSets.SetCheck

/-!
# N663: a (64, 18, 2) SDS in C₂ × C₄ × C₈

Open in Gordon's table (`SDS(64,18,2,[2,4,8])`, 2026-11-05). The set is object O51
(`objects/O51.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N663

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O51's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x98260418400210e

set_option linter.style.longLine false in
/-- Object O51's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x110010

/-- Object O51: the sign of each element. -/
def sds : ZMod 2 × ZMod 4 × ZMod 8 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 18 2 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 4 × ZMod 8)
    (P := plus) (N := minus) (by decide +kernel)

/-- N663: C₂ × C₄ × C₈ has a signed difference set with
parameters (64, 18, 2). -/
theorem hasSDS :
    HasSDS (ZMod 2 × ZMod 4 × ZMod 8) 18 2 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N663
