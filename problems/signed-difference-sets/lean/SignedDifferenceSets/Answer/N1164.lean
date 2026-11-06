module

public import SignedDifferenceSets.SetCheck

/-!
# N1164: a (79, 61, 38) SDS in C₇₉

Open in Gordon's table (`SDS(79,61,38,[79])`, 2026-11-05). The set is object O34
(`objects/O34.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N1164

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O34's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x5fa67be2eafdb7f2f7ff

set_option linter.style.longLine false in
/-- Object O34's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x108000000008000000

/-- Object O34: the sign of each element. -/
def sds : ZMod 79 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 61 38 sds :=
  isSDS_of_checkSet (G := ZMod 79)
    (P := plus) (N := minus) (by decide +kernel)

/-- N1164: C₇₉ has a signed difference set with
parameters (79, 61, 38). -/
theorem hasSDS :
    HasSDS (ZMod 79) 61 38 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N1164
