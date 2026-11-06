module

public import SignedDifferenceSets.SetCheck

/-!
# N24177: a (300, 55, 6) SDS in C₃₀₀

Open in Gordon's table (`SDS(300,55,6,[300])`, 2026-11-05). The set is object O39
(`objects/O39.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N24177

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O39's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x200880610e01020410400044006a712100026000002010400001400080a0803400090290122

set_option linter.style.longLine false in
/-- Object O39's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x400000000000100000000000040000000000010000000000004000000000001

/-- Object O39: the sign of each element. -/
def sds : ZMod 300 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 55 6 sds :=
  isSDS_of_checkSet (G := ZMod 300)
    (P := plus) (N := minus) (by decide +kernel)

/-- N24177: C₃₀₀ has a signed difference set with
parameters (300, 55, 6). -/
theorem hasSDS :
    HasSDS (ZMod 300) 55 6 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N24177
