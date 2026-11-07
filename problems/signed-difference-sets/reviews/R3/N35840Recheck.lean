module

public import SignedDifferenceSets.SetCheck

/-!
# N35840: a (361, 316, 141) SDS in C₁₉ × C₁₉

Open in Gordon's table (`SDS(361,316,141,[19,19])`, 2026-11-05). The set is object O12
(`objects/O12.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace RefuterCopy.N35840
open SignedDifferenceSets

-- A literal cannot span lines.
set_option linter.style.longLine false in
/-- Object O12's plus elements, as bits over the element numbers of `Indexed`. -/
def plus : ℕ := 0x1ddefedd67c6fbbfff2e7dffedeffffbed5aff3bffafe6dcfdd7ffe4afcf8bd6eebbf1e7fdfbbbf9fe97becf50d

set_option linter.style.longLine false in
/-- Object O12's minus elements, as bits over the element numbers of `Indexed`. -/
def minus : ℕ := 0x2100201020004000c082001010000012800044004010200028001200200408004006000004440200084030af2

/-- Object O12: the sign of each element. -/
def sds : ZMod 19 × ZMod 19 → SignType := fun x => ofMasks plus minus (Indexed.equiv x)

set_option maxRecDepth 100000 in
-- `decide +kernel` evaluates `checkSet`: the count and every shift's signed count.
theorem isSDS : IsSDS 316 141 sds :=
  isSDS_of_checkSet (G := ZMod 19 × ZMod 19) (P := plus) (N := minus) (by decide +kernel)

/-- N35840: C₁₉ × C₁₉ has a signed difference set with parameters (361, 316, 141). -/
theorem hasSDS : HasSDS (ZMod 19 × ZMod 19) 316 141 := ⟨sds, isSDS⟩

#print axioms hasSDS
end RefuterCopy.N35840
