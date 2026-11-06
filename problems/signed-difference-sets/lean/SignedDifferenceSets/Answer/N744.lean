module

public import SignedDifferenceSets.SetCheck

/-!
# N744: a (64, 46, 30) SDS in C₈ × C₈

Open in Gordon's table (`SDS(64,46,30,[8,8])`, 2026-11-05). The set is object O30
(`objects/O30.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N744

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O30's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x7eebdebbf6affc54

set_option linter.style.longLine false in
/-- Object O30's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O30: the sign of each element. -/
def sds : ZMod 8 × ZMod 8 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 46 30 sds :=
  isSDS_of_checkSet (G := ZMod 8 × ZMod 8) (P := plus) (N := minus) (by decide +kernel)

/-- N744: C₈ × C₈ has a signed difference set with parameters (64, 46, 30). -/
theorem hasSDS : HasSDS (ZMod 8 × ZMod 8) 46 30 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N744
