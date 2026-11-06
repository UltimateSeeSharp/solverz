module

public import SignedDifferenceSets.SetCheck

/-!
# N735: a (64, 46, 30) SDS in C₂ × C₂ × C₂ × C₂ × C₂ × C₂

Open in Gordon's table (`SDS(64,46,30,[2,2,2,2,2,2])`, 2026-11-05). The set is object O28
(`objects/O28.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N735

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O28's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x7dbedb7eb7deeee0

set_option linter.style.longLine false in
/-- Object O28's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O28: the sign of each element. -/
def sds : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 46 30 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)
    (P := plus) (N := minus) (by decide +kernel)

/-- N735: C₂ × C₂ × C₂ × C₂ × C₂ × C₂ has a signed difference set with parameters (64, 46, 30). -/
theorem hasSDS : HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) 46 30 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N735
