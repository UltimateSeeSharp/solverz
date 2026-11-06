module

public import SignedDifferenceSets.SetCheck

/-!
# N17201: a (256, 154, 90) SDS in C₂ × C₂ × C₂ × C₂ × C₂ × C₂ × C₂ × C₂

Open in Gordon's table (`SDS(256,154,90,[2,2,2,2,2,2,2,2])`, 2026-11-05). The set is object O32
(`objects/O32.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N17201

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O32's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xa1b0bfdcdbfaf90fd73ff6c9fd432c1fda75d5f77b28b733999a567d5432947e

set_option linter.style.longLine false in
/-- Object O32's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O32: the sign of each element. -/
def sds : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 154 90 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)
    (P := plus) (N := minus) (by decide +kernel)

/-- N17201: C₂ × C₂ × C₂ × C₂ × C₂ × C₂ × C₂ × C₂ has a signed difference set with
parameters (256, 154, 90). -/
theorem hasSDS :
    HasSDS (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) 154 90 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N17201
