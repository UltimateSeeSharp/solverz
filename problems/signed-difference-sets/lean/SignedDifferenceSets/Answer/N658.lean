module

public import SignedDifferenceSets.SetCheck

/-!
# N658: a (64, 18, 2) SDS in C₂ × C₂ × C₂ × C₂ × C₂ × C₂

Open in Gordon's table (`SDS(64,18,2,[2,2,2,2,2,2])`, 2026-11-05). The set is object O47
(`objects/O47.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N658

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O47's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x84202412140111e

set_option linter.style.longLine false in
/-- Object O47's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1000800000080000

/-- Object O47: the sign of each element. -/
def sds : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 18 2 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)
    (P := plus) (N := minus) (by decide +kernel)

/-- N658: C₂ × C₂ × C₂ × C₂ × C₂ × C₂ has a signed difference set with
parameters (64, 18, 2). -/
theorem hasSDS :
    HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) 18 2 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N658
