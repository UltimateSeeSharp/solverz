module

public import SignedDifferenceSets.SetCheck

/-!
# N388: a (51, 19, 3) SDS in C₅₁

Open in Gordon's table (`SDS(51,19,3,[51])`, 2026-11-05). The set is object O69
(`objects/O69.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N388

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O69's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x400020001

set_option linter.style.longLine false in
/-- Object O69's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x5127034c6a0

/-- Object O69: the sign of each element. -/
def sds : ZMod 51 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 19 3 sds :=
  isSDS_of_checkSet (G := ZMod 51)
    (P := plus) (N := minus) (by decide +kernel)

/-- N388: C₅₁ has a signed difference set with
parameters (51, 19, 3). -/
theorem hasSDS :
    HasSDS (ZMod 51) 19 3 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N388
