module

public import SignedDifferenceSets.SetCheck

/-!
# N3539: a (128, 68, 4) SDS in C₂ × C₂ × C₂ × C₂ × C₂ × C₂ × C₂

Open in Gordon's table (`SDS(128,68,4,[2,2,2,2,2,2,2])`, 2026-11-05). The set is object O81
(`objects/O81.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N3539

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O81's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x9c222c1a540111e284603452161953f

set_option linter.style.longLine false in
/-- Object O81's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x30048104002984211180a08084080000

/-- Object O81: the sign of each element. -/
def sds : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 68 4 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)
    (P := plus) (N := minus) (by decide +kernel)

/-- N3539: C₂ × C₂ × C₂ × C₂ × C₂ × C₂ × C₂ has a signed difference set with
parameters (128, 68, 4). -/
theorem hasSDS :
    HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) 68 4 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N3539
