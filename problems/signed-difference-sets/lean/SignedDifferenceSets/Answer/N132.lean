module

public import SignedDifferenceSets.SetCheck

/-!
# N132: a (32, 20, 4) SDS in C₄ × C₈

Open in Gordon's table (`SDS(32,20,4,[4,8])`, 2026-11-05). The set is object O18
(`objects/O18.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N132

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O18's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x564ef681

set_option linter.style.longLine false in
/-- Object O18's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0xa0300000

/-- Object O18: the sign of each element. -/
def sds : ZMod 4 × ZMod 8 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 20 4 sds :=
  isSDS_of_checkSet (G := ZMod 4 × ZMod 8) (P := plus) (N := minus) (by decide +kernel)

/-- N132: C₄ × C₈ has a signed difference set with parameters (32, 20, 4). -/
theorem hasSDS : HasSDS (ZMod 4 × ZMod 8) 20 4 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N132
