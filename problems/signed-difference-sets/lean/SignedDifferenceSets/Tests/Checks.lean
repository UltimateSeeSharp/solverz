module

public import SignedDifferenceSets.ContractionCheck
public import SignedDifferenceSets.SetCheck

/-!
# Tests for the kernel checks

`checkSet` accepts known sets (cyclic and a product) and rejects each with one sign flipped.
`noVector` is `false` where a set exists (its coset sums are such a vector) and proves N32
again. Its node count equals the solver's (E5), so both search the same tree.
-/

@[expose] public section

namespace SignedDifferenceSets.Tests

-- O4, the (5, 4, −1) SDS in C₅ (−, +, +, −, 0): plus = {1, 2}, minus = {0, 3}.
example : checkSet (ZMod 5) 4 (-1) 6 9 = true := by decide +kernel
-- O4 with element 1 flipped to −.
example : checkSet (ZMod 5) 4 (-1) 4 11 = false := by decide +kernel
-- O5, the (9, 8, −1) SDS in C₃ × C₃, as bits over `Indexed`'s numbers (3a + b).
example : checkSet (ZMod 3 × ZMod 3) 8 (-1) 228 27 = true := by decide +kernel
-- O5 with (0, 2) flipped to −.
example : checkSet (ZMod 3 × ZMod 3) 8 (-1) 224 31 = false := by decide +kernel

-- N49 (O6) exists, so its coset sums on C₅ (c = 5) are a vector: Q = 12 + 4, t = 5, s = 6.
example : noVector 5 (Indexed.addIdx (ZMod 1 × ZMod 5)) 5 16 5 12 6 = false := by decide +kernel
-- N61 (O7) exists: coset sums on C₃ (c = 9), Q = 10 + 8, t = 9, s = 6.
example : noVector 3 (Indexed.addIdx (ZMod 1 × ZMod 1 × ZMod 3)) 9 18 9 10 6 = false := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- N32 (Z2) again, through `not_hasSDS_of_noVector` along C₂ × C₁₀ → C₅. -/
example : ¬ HasSDS (ZMod 2 × ZMod 10) 17 8 :=
  not_hasSDS_of_noVector (.prod (.cast 1 (by norm_num)) (.cast 5 (by norm_num))) 4 13
    (by simp [Fintype.card_prod, ZMod.card]) (by norm_num [Fintype.card_prod, ZMod.card])
    (by decide +kernel)

/-- `f lo + f (lo + 1) + ⋯` over `m` integers. -/
def natSumRange (f : ℤ → ℕ) (lo : ℤ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => f lo + natSumRange f (lo + 1) m

/-- The calls `go` makes, counted as the solver counts its nodes. -/
def goNodes (c Q s top : ℤ) : ℕ → ℤ → ℤ → ℕ
  | 0, _, _ => 1
  | rem + 1, sum, sq =>
    if cut c Q s (rem + 1) sum sq then 1 else
      1 + natSumRange (fun x => if Q - sq < x * x then 0 else
        goNodes c Q s top rem (sum + x) (sq + x * x)) (-top) (2 * top + 1).toNat

/-- The calls `noVector` makes, root included. -/
def noVectorNodes (n : ℕ) (c Q s : ℤ) : ℕ :=
  if cut c Q s n 0 0 then 1 else
    1 + natSumRange (fun x => if Q < x * x then 0 else goNodes c Q s |x| (n - 1) x (x * x))
      (-c) (2 * c + 1).toNat

-- E5's node counts: N95 (C₇, c = 4, Q = 49, s = 17), N168 (C₉, c = 4, Q = 17, s = 9).
example : noVectorNodes 7 4 49 17 = 3924 := by decide +kernel
example : noVectorNodes 9 4 17 9 = 16078 := by decide +kernel

end SignedDifferenceSets.Tests
