module

public import SignedDifferenceSets.SetCheck

/-!
# N1008: a (75, 26, 1) SDS in C₅ × C₁₅

Open in Gordon's table (`SDS(75,26,1,[5,15])`, 2026-11-05). The set is object O62
(`objects/O62.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N1008

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O62's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x814c008260208124b2

set_option linter.style.longLine false in
/-- Object O62's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x2020004400c00500000

/-- Object O62: the sign of each element. -/
def sds : ZMod 5 × ZMod 15 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 26 1 sds :=
  isSDS_of_checkSet (G := ZMod 5 × ZMod 15)
    (P := plus) (N := minus) (by decide +kernel)

/-- N1008: C₅ × C₁₅ has a signed difference set with
parameters (75, 26, 1). -/
theorem hasSDS :
    HasSDS (ZMod 5 × ZMod 15) 26 1 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N1008
