module

public import SignedDifferenceSets.SetCheck

/-!
# N638: a (63, 47, 11) SDS in C₃ × C₂₁

Open in Gordon's table (`SDS(63,47,11,[3,21])`, 2026-11-05). The set is object O25
(`objects/O25.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N638

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O25's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x25b45e6136fb3d7e

set_option linter.style.longLine false in
/-- Object O25's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x4802810c80004080

/-- Object O25: the sign of each element. -/
def sds : ZMod 3 × ZMod 21 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 47 11 sds :=
  isSDS_of_checkSet (G := ZMod 3 × ZMod 21) (P := plus) (N := minus) (by decide +kernel)

/-- N638: C₃ × C₂₁ has a signed difference set with parameters (63, 47, 11). -/
theorem hasSDS : HasSDS (ZMod 3 × ZMod 21) 47 11 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N638
