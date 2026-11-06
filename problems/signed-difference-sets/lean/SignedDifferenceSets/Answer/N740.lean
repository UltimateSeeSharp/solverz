module

public import SignedDifferenceSets.SetCheck

/-!
# N740: a (64, 46, 30) SDS in C₂ × C₄ × C₈

Open in Gordon's table (`SDS(64,46,30,[2,4,8])`, 2026-11-05). The set is object O55
(`objects/O55.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N740

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O55's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xf67d9fbe7beedee0

set_option linter.style.longLine false in
/-- Object O55's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O55: the sign of each element. -/
def sds : ZMod 2 × ZMod 4 × ZMod 8 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 46 30 sds :=
  isSDS_of_checkSet (G := ZMod 2 × ZMod 4 × ZMod 8)
    (P := plus) (N := minus) (by decide +kernel)

/-- N740: C₂ × C₄ × C₈ has a signed difference set with
parameters (64, 46, 30). -/
theorem hasSDS :
    HasSDS (ZMod 2 × ZMod 4 × ZMod 8) 46 30 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N740
