module

public import SignedDifferenceSets.SetCheck

/-!
# N286: a (45, 37, 1) SDS in C₃ × C₁₅

Open in Gordon's table (`SDS(45,37,1,[3,15])`, 2026-11-05). The set is object O23
(`objects/O23.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N286

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O23's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x8f5ac8f0537

set_option linter.style.longLine false in
/-- Object O23's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x170a53708000

/-- Object O23: the sign of each element. -/
def sds : ZMod 3 × ZMod 15 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 37 1 sds :=
  isSDS_of_checkSet (G := ZMod 3 × ZMod 15) (P := plus) (N := minus) (by decide +kernel)

/-- N286: C₃ × C₁₅ has a signed difference set with parameters (45, 37, 1). -/
theorem hasSDS : HasSDS (ZMod 3 × ZMod 15) 37 1 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N286
