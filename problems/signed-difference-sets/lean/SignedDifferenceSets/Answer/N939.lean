module

public import SignedDifferenceSets.SetCheck

/-!
# N939: a (72, 48, 12) SDS in C₃ × C₂₄

Open in Gordon's table (`SDS(72,48,12,[3,24])`, 2026-11-05). The set is object O104
(`objects/O104.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N939

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O104's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x7fd5e4d56f4f318308

set_option linter.style.longLine false in
/-- Object O104's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x219209010000010

/-- Object O104: the sign of each element. -/
def sds : ZMod 3 × ZMod 24 → SignType :=
  fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 48 12 sds :=
  isSDS_of_checkSet (G := ZMod 3 × ZMod 24)
    (P := plus) (N := minus) (by decide +kernel)

/-- N939: C₃ × C₂₄ has a signed difference set with
parameters (72, 48, 12). -/
theorem hasSDS :
    HasSDS (ZMod 3 × ZMod 24) 48 12 :=
  ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N939
