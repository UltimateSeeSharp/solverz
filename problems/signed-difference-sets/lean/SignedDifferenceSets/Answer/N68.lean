module

public import SignedDifferenceSets.Check

/-!
# N68: a (27, 14, 5) SDS in C₃ × C₉

Open in Gordon's table (`SDS(27,14,5,[3,9])`, 2026-11-05). The set is object O10
(`objects/O10.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N68

/-- Object O10: the sign of each element, first coordinate outermost. -/
def sds : ZMod 3 × ZMod 9 → SignType := fun p =>
  (![![1, 0, 0, 0, 0, 0, 0, 0, 1],
    ![0, 1, 0, 0, 1, 1, 1, 1, 0],
    ![0, 1, -1, 1, 1, 1, 0, 1, 1]])
    p.1 p.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `decide` evaluates the definition: every shift's signed count.
theorem isSDS : IsSDS 14 5 sds := by decide

/-- N68: C₃ × C₉ has a signed difference set with parameters (27, 14, 5). -/
theorem hasSDS : HasSDS (ZMod 3 × ZMod 9) 14 5 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N68
