module

public import SignedDifferenceSets.SetCheck

/-!
# N931: a (72, 40, 4) SDS in C₂ × C₆ × C₆

Open in Gordon's table (`SDS(72,40,4,[2,6,6])`, 2026-11-05). The set is object O84
(`objects/O84.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N931

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O84's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xf47213829f44210817

set_option linter.style.longLine false in
/-- Object O84's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x80000016083003028

/-- Object O84: the sign of each element. -/
def sds : ZMod 2 × ZMod 6 × ZMod 6 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 40 4 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 6 × ZMod 6)
    (P := plus) (N := minus) (by decide +kernel)

/-- N931: C₂ × C₆ × C₆ has a signed difference set with
parameters (72, 40, 4). -/
theorem hasSDS :
    HasSDS (ZMod 2 × ZMod 6 × ZMod 6) 40 4 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N931
