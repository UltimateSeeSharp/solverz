module

public import SignedDifferenceSets.SetCheck

/-!
# N170: a (36, 11, 2) SDS in C₆ × C₆

Open in Gordon's table (`SDS(36,11,2,[6,6])`, 2026-11-05). The set is object O22
(`objects/O22.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N170

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O22's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xf44210801

set_option linter.style.longLine false in
/-- Object O22's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x80000000

/-- Object O22: the sign of each element. -/
def sds : ZMod 6 × ZMod 6 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 11 2 sds :=
  isSDS_of_checkSet (G := ZMod 6 × ZMod 6) (P := plus) (N := minus) (by decide +kernel)

/-- N170: C₆ × C₆ has a signed difference set with parameters (36, 11, 2). -/
theorem hasSDS : HasSDS (ZMod 6 × ZMod 6) 11 2 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N170
