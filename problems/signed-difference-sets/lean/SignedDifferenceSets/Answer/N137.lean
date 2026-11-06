module

public import SignedDifferenceSets.SetCheck

/-!
# N137: a (32, 28, 12) SDS in C₂ × C₄ × C₄

Open in Gordon's table (`SDS(32,28,12,[2,4,4])`, 2026-11-05). The set is object O19
(`objects/O19.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N137

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O19's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xe37ff5f5

set_option linter.style.longLine false in
/-- Object O19's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1c800000

/-- Object O19: the sign of each element. -/
def sds : ZMod 2 × ZMod 4 × ZMod 4 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 28 12 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 4 × ZMod 4) (P := plus) (N := minus) (by decide +kernel)

/-- N137: C₂ × C₄ × C₄ has a signed difference set with parameters (32, 28, 12). -/
theorem hasSDS : HasSDS (ZMod 2 × ZMod 4 × ZMod 4) 28 12 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N137
