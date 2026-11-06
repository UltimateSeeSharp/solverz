module

public import SignedDifferenceSets.SetCheck

/-!
# N665: a (64, 18, 2) SDS in C₄ × C₄ × C₄

Open in Gordon's table (`SDS(64,18,2,[4,4,4])`, 2026-11-05). The set is object O52
(`objects/O52.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N665

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O52's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x8049050080131216

set_option linter.style.longLine false in
/-- Object O52's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x208000000400

/-- Object O52: the sign of each element. -/
def sds : ZMod 4 × ZMod 4 × ZMod 4 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 18 2 sds :=
  isSDS_of_checkSet (G := ZMod 4 × ZMod 4 × ZMod 4)
    (P := plus) (N := minus) (by decide +kernel)

/-- N665: C₄ × C₄ × C₄ has a signed difference set with
parameters (64, 18, 2). -/
theorem hasSDS :
    HasSDS (ZMod 4 × ZMod 4 × ZMod 4) 18 2 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N665
