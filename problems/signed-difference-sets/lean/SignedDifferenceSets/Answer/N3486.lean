module

public import SignedDifferenceSets.SetCheck

/-!
# N3486: a (127, 109, 90) SDS in C₁₂₇

Open in Gordon's table (`SDS(127,109,90,[127])`, 2026-11-05). The set is object O35
(`objects/O35.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N3486

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O35's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x37dfeffffffefdeebef6ffd7bf2ffffe

set_option linter.style.longLine false in
/-- Object O35's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x1

/-- Object O35: the sign of each element. -/
def sds : ZMod 127 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 109 90 sds :=
  isSDS_of_checkSet (G := ZMod 127)
    (P := plus) (N := minus) (by decide +kernel)

/-- N3486: C₁₂₇ has a signed difference set with
parameters (127, 109, 90). -/
theorem hasSDS :
    HasSDS (ZMod 127) 109 90 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N3486
