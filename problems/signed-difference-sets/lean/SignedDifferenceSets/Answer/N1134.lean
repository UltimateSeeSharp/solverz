module

public import SignedDifferenceSets.SetCheck

/-!
# N1134: a (78, 53, 28) SDS in C₇₈

Open in Gordon's table (`SDS(78,53,28,[78])`, 2026-11-05). The set is object O59
(`objects/O59.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N1134

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O59's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x3ffb7be30be5d33d4eca

set_option linter.style.longLine false in
/-- Object O59's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x10000004000001

/-- Object O59: the sign of each element. -/
def sds : ZMod 78 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 53 28 sds :=
  isSDS_of_checkSet (G := ZMod 78)
    (P := plus) (N := minus) (by decide +kernel)

/-- N1134: C₇₈ has a signed difference set with
parameters (78, 53, 28). -/
theorem hasSDS :
    HasSDS (ZMod 78) 53 28 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N1134
