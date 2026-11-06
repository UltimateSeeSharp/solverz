module

public import SignedDifferenceSets.Check

/-!
# N19: a (18, 13, 4) SDS in C₃ × C₆

Open in Gordon's table (`SDS(18,13,4,[3,6])`, 2026-11-05). The set is object O100
(`objects/O100.txt`); this file is generated from it by `solver/answer.py`.
-/

@[expose] public section

namespace SignedDifferenceSets.Answer.N19

/-- Object O100: the sign of each element, first coordinate outermost. -/
def sds : ZMod 3 × ZMod 6 → SignType := fun p =>
  (![![1, 1, 0, 1, 1, 1],
    ![1, 0, 0, 1, 1, -1],
    ![1, 0, 0, -1, 1, 1]])
    p.1 p.2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- `decide` evaluates the definition: every shift's signed count.
theorem isSDS : IsSDS 13 4 sds := by decide

/-- N19: C₃ × C₆ has a signed difference set with parameters (18, 13, 4). -/
theorem hasSDS : HasSDS (ZMod 3 × ZMod 6) 13 4 := ⟨sds, isSDS⟩

end SignedDifferenceSets.Answer.N19
