module

public import SignedDifferenceSets.SetCheck

/-!
# N934: a (72, 40, 4) SDS in C₆ × C₁₂

Open in Gordon's table (`SDS(72,40,4,[6,12])`, 2026-11-05). The set is object O83
(`objects/O83.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N934

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O83's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xcd6182821ed41a0c47

set_option linter.style.longLine false in
/-- Object O83's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x20802044600a002020

/-- Object O83: the sign of each element. -/
def sds : ZMod 6 × ZMod 12 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 40 4 sds :=
  isSDS_of_checkSet (G := ZMod 6 × ZMod 12)
    (P := plus) (N := minus) (by decide +kernel)

/-- N934: C₆ × C₁₂ has a signed difference set with
parameters (72, 40, 4). -/
theorem hasSDS :
    HasSDS (ZMod 6 × ZMod 12) 40 4 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N934
