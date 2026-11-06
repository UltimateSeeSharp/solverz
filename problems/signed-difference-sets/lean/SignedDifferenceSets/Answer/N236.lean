module

public import SignedDifferenceSets.SetCheck

/-!
# N236: a (42, 18, 2) SDS in C₄₂

Open in Gordon's table (`SDS(42,18,2,[42])`, 2026-11-05). The set is object O61
(`objects/O61.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N236

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O61's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x8000008201

set_option linter.style.longLine false in
/-- Object O61's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1a592450c8

/-- Object O61: the sign of each element. -/
def sds : ZMod 42 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 18 2 sds :=
  isSDS_of_checkSet (G := ZMod 42)
    (P := plus) (N := minus) (by decide +kernel)

/-- N236: C₄₂ has a signed difference set with
parameters (42, 18, 2). -/
theorem hasSDS :
    HasSDS (ZMod 42) 18 2 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N236
