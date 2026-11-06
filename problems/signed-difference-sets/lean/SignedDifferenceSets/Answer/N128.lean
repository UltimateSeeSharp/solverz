module

public import SignedDifferenceSets.SetCheck

/-!
# N128: a (32, 20, 4) SDS in C₂ × C₂ × C₂ × C₄

Open in Gordon's table (`SDS(32,20,4,[2,2,2,4])`, 2026-11-05). The set is object O15
(`objects/O15.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N128

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O15's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x3a1e7e81

set_option linter.style.longLine false in
/-- Object O15's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x44600000

/-- Object O15: the sign of each element. -/
def sds : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 4 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 20 4 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 4)
    (P := plus) (N := minus) (by decide +kernel)

/-- N128: C₂ × C₂ × C₂ × C₄ has a signed difference set with parameters (32, 20, 4). -/
theorem hasSDS : HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 4) 20 4 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N128
