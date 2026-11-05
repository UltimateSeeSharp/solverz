module

public import SignedDifferenceSets.Check

/-!
# Tests for the goal's definitions

`IsSDS` accepts known signed difference sets of each kind (an ordinary difference set,
circulant weighing matrices, proper SDSs in cyclic and non-cyclic groups) and rejects
broken copies; `HasSDS` is decided both ways on tiny groups.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

/-- The (7, 3, 1) difference set {0, 1, 3} in ℤ₇, all signs `+`. -/
def ds731 : ZMod 7 → SignType := fun x => ![1, 1, 0, 1, 0, 0, 0] x

example : IsSDS 3 1 ds731 := by decide

/-- CW(7, 4): a circulant weighing matrix, an SDS with λ = 0 in ℤ₇. -/
def cw74 : ZMod 7 → SignType := fun x => ![-1, 1, 1, 0, 1, 0, 0] x

example : IsSDS 4 0 cw74 := by decide

/-- CW(4, 4): the circulant Hadamard matrix of order 4. -/
def cw44 : ZMod 4 → SignType := fun x => ![-1, 1, 1, 1] x

example : IsSDS 4 0 cw44 := by decide

/-- A (5, 4, −1) SDS in ℤ₅. -/
def sds541 : ZMod 5 → SignType := fun x => ![-1, 1, 1, -1, 0] x

example : IsSDS 4 (-1) sds541 := by decide

/-- A (9, 8, −1) SDS in ℤ₃ × ℤ₃ (non-cyclic): rows indexed by the first coordinate. -/
def sds981 : ZMod 3 × ZMod 3 → SignType := fun p =>
  ![![-1, -1, 1], ![-1, -1, 1], ![1, 1, 0]] p.1 p.2

example : IsSDS 8 (-1) sds981 := by decide

/-! Broken copies: one sign flipped, one element dropped, wrong parameters. -/

example : ¬ IsSDS 4 0 (fun x : ZMod 7 => ![1, 1, 1, 0, 1, 0, 0] x) := by decide
example : ¬ IsSDS 4 0 (fun x : ZMod 7 => ![-1, 1, 1, 0, 0, 0, 0] x) := by decide
example : ¬ IsSDS 3 0 cw74 := by decide
example : ¬ IsSDS 4 1 cw74 := by decide
example : ¬ IsSDS 8 (-1)
    (fun p : ZMod 3 × ZMod 3 => ![![-1, -1, 1], ![-1, 1, 1], ![1, 1, 0]] p.1 p.2) := by
  decide

/-! `HasSDS` both ways on tiny groups. -/

example : HasSDS (ZMod 7) 4 0 := ⟨cw74, by decide⟩

/-- No (4, 3, −1) SDS in ℤ₂ × ℤ₂ (the triage search found none). -/
example : ¬ HasSDS (ZMod 2 × ZMod 2) 3 (-1) := by
  decide

/-- The trivial SDS: one marked element, λ = 0. -/
example : HasSDS (ZMod 5) 1 0 := ⟨fun x => if x = 0 then 1 else 0, by decide⟩

end SignedDifferenceSets.Tests
