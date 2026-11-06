module

public import SignedDifferenceSets.SetCheck

/-!
# N159: a (35, 21, 10) SDS in C₃₅

Open in Gordon's table (`SDS(35,21,10,[35])`, 2026-11-05). The set is object O96
(`objects/O96.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N159

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O96's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x320d56f3f

set_option linter.style.longLine false in
/-- Object O96's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x80

/-- Object O96: the sign of each element. -/
def sds : ZMod 35 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 21 10 sds :=
  isSDS_of_checkSet (G := ZMod 35)
    (P := plus) (N := minus) (by decide +kernel)

/-- N159: C₃₅ has a signed difference set with
parameters (35, 21, 10). -/
theorem hasSDS :
    HasSDS (ZMod 35) 21 10 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N159
