module

public import SignedDifferenceSets.SetCheck

/-!
# N139: a (32, 28, 12) SDS in C₄ × C₈

Open in Gordon's table (`SDS(32,28,12,[4,8])`, 2026-11-05). The set is object O20
(`objects/O20.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N139

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O20's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xfe8dbfdd

set_option linter.style.longLine false in
/-- Object O20's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1504000

/-- Object O20: the sign of each element. -/
def sds : ZMod 4 × ZMod 8 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 28 12 sds :=
  isSDS_of_checkSet (G := ZMod 4 × ZMod 8) (P := plus) (N := minus) (by decide +kernel)

/-- N139: C₄ × C₈ has a signed difference set with parameters (32, 28, 12). -/
theorem hasSDS : HasSDS (ZMod 4 × ZMod 8) 28 12 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N139
