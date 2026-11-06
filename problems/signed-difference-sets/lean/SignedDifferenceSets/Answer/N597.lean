module

public import SignedDifferenceSets.SetCheck

/-!
# N597: a (61, 49, 36) SDS in C₆₁

Open in Gordon's table (`SDS(61,49,36,[61])`, 2026-11-05). The set is object O97
(`objects/O97.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N597

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O97's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0xf56effbff7b2ffe

set_option linter.style.longLine false in
/-- Object O97's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O97: the sign of each element. -/
def sds : ZMod 61 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 49 36 sds :=
  isSDS_of_checkSet (G := ZMod 61)
    (P := plus) (N := minus) (by decide +kernel)

/-- N597: C₆₁ has a signed difference set with
parameters (61, 49, 36). -/
theorem hasSDS :
    HasSDS (ZMod 61) 49 36 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N597
