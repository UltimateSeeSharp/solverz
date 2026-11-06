module

public import SignedDifferenceSets.SetCheck

/-!
# N352: a (49, 33, 1) SDS in C₇ × C₇

Open in Gordon's table (`SDS(49,33,1,[7,7])`, 2026-11-05). The set is object O24
(`objects/O24.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N352

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O24's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x14113119145fe

set_option linter.style.longLine false in
/-- Object O24's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x18a062448a00

/-- Object O24: the sign of each element. -/
def sds : ZMod 7 × ZMod 7 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 33 1 sds :=
  isSDS_of_checkSet (G := ZMod 7 × ZMod 7) (P := plus) (N := minus) (by decide +kernel)

/-- N352: C₇ × C₇ has a signed difference set with parameters (49, 33, 1). -/
theorem hasSDS : HasSDS (ZMod 7 × ZMod 7) 33 1 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N352
